/-
  NockvmE2E/Exec/E2EMain.lean   (proof-only)

  Assembly of `exec_e2e`: the flat verifier `verifyFlat` run on the flat views of the audited random oracle is contained, table by
  table, in the audited succinct verifier (`verifyFlat_sound_tab`), and `exec_e2e_of_pointwise` turns that into the `2^-82` bound.
-/
import NockvmE2E.Exec.E2E
import NockvmE2E.Exec.E2EEmbed
import NockvmE2E.Exec.E2EEmbed2
import NockvmE2E.Exec.E2ELinksRap
import NockvmE2E.Exec.E2ELinksFri

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

namespace NockvmE2E.Exec.E2EMain

open NockvmE2E.Exec NockvmE2E.Exec.V NockvmE2E.Exec.VL NockvmE2E.Merkle NockvmE2E.Exec.E2E NockvmE2E.Exec.Emb NockvmE2E.FriPort

section Route

variable {Dg : Type} [Finite Dg] [DecidableEq Dg] {Op : Type} [Finite Op] [DecidableEq Op]
  {Query : Type} {Statement Salt : Type} {ms : MRounds Dg}

/-- the hash half of the table, routed through `hashQueriesK` -/
theorem tabK_hroute (gAll : (d : Query ⊕ Key (Statement × Salt) PUnit (compiledRoundsK Dg Op ms)) →
      succinctRange Dg Op Query Statement Salt ms d) {α : Type} (oa : OracleComp (Query →ₒ Dg) α) :
    tabEval (tabK gAll) (simulateQ (hashQueriesK (Query := Query) (Statement := Statement) (Salt := Salt) (Op := Op) (ms := ms)) oa) =
      tabEval (spec := Query →ₒ Dg) (fun q => some (gAll (.inl q))) oa := by
  induction oa using OracleComp.inductionOn with
  | pure a => simp [tabEval_pure]
  | query_bind t k ih =>
    have h1 : simulateQ (hashQueriesK (Query := Query) (Statement := Statement) (Salt := Salt) (Op := Op) (ms := ms))
        (liftM ((Query →ₒ Dg).query t) >>= k) =
      (liftM ((SuccinctSpecK Dg Op Query Statement Salt ms).query (.inr (.inl t))) :
        OracleComp (SuccinctSpecK Dg Op Query Statement Salt ms) _) >>= fun r =>
          simulateQ (hashQueriesK (Query := Query) (Statement := Statement) (Salt := Salt) (Op := Op) (ms := ms)) (k r) := by
      simp only [simulateQ_bind, simulateQ_liftM_query]
      rfl
    rw [h1, tabEval_query_bind, tabEval_query_bind]
    simp only [tabK]
    exact ih _

/-- **the pointwise verifier evaluation**: with accept-all guards, a table `g`, the path `p` of the table on the messages, the hash
check accepted under the hash half and the local check true, the succinct verifier returns `some p`. -/
theorem tabEval_succinctVerifyK (gAll : (d : Query ⊕ Key (Statement × Salt) PUnit (compiledRoundsK Dg Op ms)) →
      succinctRange Dg Op Query Statement Salt ms d)
    (mc : List Dg → Op → OracleComp (Query →ₒ Dg) Bool)
    (la : (Statement × Salt) → (protocol (compiledRoundsK Dg Op ms)).tree.ExecutionPath → Bool)
    (z : Statement × Salt) (msgs : PublicMessages (compiledRoundsK Dg Op ms))
    (p : (protocol (compiledRoundsK Dg Op ms)).tree.ExecutionPath)
    (hp : pathOfG (fun key => gAll (.inr key)) (compiledRoundsK Dg Op ms) z msgs id (fun _ => rfl) = p)
    (hm : tabEval (spec := Query →ₒ Dg) (fun q => some (gAll (.inl q))) (mc (pathRootsK Dg Op ms p).1 (pathRootsK Dg Op ms p).2) = some true)
    (hl : la z p = true) :
    tabEval (tabK gAll) (succinctVerifyK (Query := Query) (trueGuards _) mc la z msgs) = some (some p) := by
  unfold succinctVerifyK
  rw [tabEval_bind, publicStoppedVerify_trueGuards gAll z msgs, hp]
  simp only [Option.bind_some]
  rw [tabEval_bind, tabK_hroute, hm]
  simp [tabEval_pure, hl]

end Route


/-- `XI` with the query count fixed to the literal `170` of the audited theorem (equal to `XI` under `XI.l = 170`) -/
abbrev XI170 (Xi : ExecInst) : ExecInst := { Xi with l := 170 }

section PRE
open NockvmE2E.Exec.E2ELR NockvmE2E.Succ NockvmE2E.Deep NockvmE2E.Succ.FriC NockvmE2E.FriPort.Batched
  NockvmE2E.Succ.FriDeep NockvmE2E.Lift NockvmE2E.Lift.Alternating NockvmE2E.Exec.Cover NockvmE2E.Exec.Layout NockvmE2E.Exec.SM NockvmE2E.Rap NockvmE2E.Merkle.RapFriQ NockvmE2E.Merkle.MA
section UL

open NockvmE2E.Succ NockvmE2E.Deep NockvmE2E.Succ.FriC NockvmE2E.FriPort NockvmE2E.FriPort.Batched
  NockvmE2E.Succ.FriDeep NockvmE2E.Succ.App NockvmE2E.Lift NockvmE2E.Lift.Alternating
  NockvmE2E.Exec.Inst

variable (XI : ExecInst) (H : HFn) (FS : FSFn) (zF : List Nat) (π : FlatProof) (hv : verifyFlat XI H FS zF π = true)

set_option hygiene false in
local notation "ωS" => smoothDomain XI.nD (nD_le_of_verify XI H FS zF π hv)
set_option hygiene false in
local notation "s1" => (fun _ : Fin (XI.k + 1) => (1 : ℕ+))

variable {B : Type} [Field B] [Fintype B] [DecidableEq B] [Algebra B KC] [Inhabited B]
variable [SampleableType KC] [Inhabited KC]
variable {Φ : CoinFrame} {ι : Type} [Fintype ι] [DecidableEq ι] {colRound : ι → ℕ}
  (P : DeepParams Φ KC ι (Fin (2 ^ XI.nD) → B) colRound) {r : ℕ} [NeZero r] (A : AirShape P r)
  (R0 : RapStatement Φ KC ι (Fin (2 ^ XI.nD) → B) colRound)
  (Rest : R0.M0 → DeepTr P → R0.Mfin → Coins Φ KC → Prop)
  (RestV : R0.M0 → DeepFin P (r := r) R0 → Coins Φ KC → Prop) {m : ℕ}
  (e : Fin (m + 1) ≃ (ι × Fin r) ⊕ Fin P.nq)
variable [DecidableEq (P.statement R0 Rest).M0] [Finite (P.statement R0 Rest).M0]
  [DecidableEq (friPlan (ω := ωS) P A R0 Rest RestV e).Mfin] [Finite (friPlan (ω := ωS) P A R0 Rest RestV e).Mfin]
  (I0 : OracleInterface (P.statement R0 Rest).M0)
  (I : (r : ℕ) → OracleInterface (Cols P.colRoundX (Fin (2 ^ XI.nD) → B) r))
  (Ifin : OracleInterface (friPlan (ω := ωS) P A R0 Rest RestV e).Mfin)
variable (d : ℕ+)
variable [∀ j, SampleableType ((pSpec XI.k (ω := ωS) s1 XI.l).Challenge j)]
variable {S : Type} [Fintype S] [Nonempty S] [SampleableType S]
variable (G : CoreDefinitions.Generator S (Fin (m + 1)) KC)
variable (Dg : Type) [Finite Dg] [DecidableEq Dg] (enc : KC ↪ Dg)
  (md : PointMaskData P.colRoundX (Fin (2 ^ XI.nD)) B Dg) (L : Fri.FriLeaves (ω := ωS) s1)
variable (hdom : 2 ^ (∑ j, ((s1) j).val) * d.val ≤ 2 ^ XI.nD)
variable (Op : Type) [Finite Op] [DecidableEq Op]
variable (PR : Array VF.K3 → Array VF.G → Prop)

set_option hygiene false in
local notation "MC" => msC P A R0 Rest RestV e I0 I Ifin 4 s1 d XI.l Dg enc md L (S := S)
set_option hygiene false in
local notation "PS" => P.statement R0 Rest
set_option hygiene false in
local notation "PL" => friPlan (ω := ωS) P A R0 Rest RestV e
set_option hygiene false in
local notation "RM" => RapP.rapMask Φ KC md.toRapMaskData (P.statement R0 Rest).M0
  (friPlan (ω := ωS) P A R0 Rest RestV e).Mfin I0 I Ifin 4
set_option hygiene false in
local notation "BM" => bmask (S := S) s1 d XI.l Dg enc L


variable (decode : Op → OpenAll Dg (merkleSkels (MC)))
  {Op' : Type}

set_option quotPrecheck false in
set_option hygiene false in
local notation "PATH" => (protocol (compiledRoundsK Dg Op (MC))).tree.ExecutionPath
set_option hygiene false in
local notation "CHI" p => chiQ P A R0 Rest RestV e I0 I Ifin 4 s1 d XI.l Dg enc md L
  (q0P P A R0 Rest RestV e I0 I Ifin 4 s1 d XI.l Dg enc md L Op decode p)
set_option hygiene false in
local notation "FINM" p => finMQ P A R0 Rest RestV e I0 I Ifin 4 s1 d XI.l Dg enc md L
  (q0P P A R0 Rest RestV e I0 I Ifin 4 s1 d XI.l Dg enc md L Op decode p)

set_option hygiene false in
local notation "FM" => Fri.friMerkleMask s1 d XI.l L Dg enc
/-- **`UniLinks'`** ('s `UniLinks` WITHOUT the uninhabitable `hxsU`): every field is about the INSTANCE only (the codecs `ds`, the decoder `vTOf`, `P`, `A`, `XI`); the proof `π`
and the table `g` never occur: flat data (`vT`, `vQ`, `ζ`, `slots`, the encoded challenges) is universally quantified, the audited
challenges are universally quantified `c0..c3`. `ds` lists the decoders of the RAP prefix in order: `ds.1` (M0, clear), `ds.2.1 … ds.2.2.2.2.1`
(the four block-challenge codecs), `ds.2.2.2.2.2.1` (Mfin, clear). -/
structure UniLinks' (dY : List ℕ → Dg) (ds : MDec (MC)) (vTOf : Array (Array VF.K3) → ι × Fin r → KC) : Prop where
  hPa : Φ.sampledAfter P.a = 2
  hPz : Φ.sampledAfter P.z = 3
  /-- α = the K3 of the limbs of block 2's challenge -/
  hαC : ∀ c : Block Φ KC 2, toKV (VF.K3.ofLimbs (ds.2.2.2.1.encC c)) = c ⟨P.a, hPa⟩
  /-- ζ = the K3 of the limbs of block 3's challenge -/
  hζC : ∀ c : Block Φ KC 3, toKV (VF.K3.ofLimbs (ds.2.2.2.2.1.encC c)) = c ⟨P.z, hPz⟩
  /-- the `Mfin` decoder reads `vQ` and `vT` -/
  hQU : ∀ vT vQ, VShape XI vT vQ → ∀ j : Fin P.nq, (ds.2.2.2.2.2.1.decM (deepMsg vT vQ)).2.2 j = toKV vQ[j.1]!
  hVT : ∀ vT vQ, VShape XI vT vQ → (ds.2.2.2.2.2.1.decM (deepMsg vT vQ)).2.1 = vTOf vT
  hlenU : ∀ slots ζ vT, (termsAt XI slots ζ vT).length = P.ns
  hdagU : ∀ (c0 : Block Φ KC 0) (c1 : Block Φ KC 1) (c2 : Block Φ KC 2) (c3 : Block Φ KC 3) (ζ : VF.K3) (vT : Array (Array VF.K3)),
    CanonIn (slotsAt XI (ds.2.1.encC c0) (ds.2.2.1.encC c1)) ζ vT →
    ∀ i : Fin P.ns, (termsAt XI (slotsAt XI (ds.2.1.encC c0) (ds.2.2.1.encC c1)) ζ vT)[i.1]? =
      some (A.Cv (chiOfBlocks c0 c1 c2 c3) (toKV ζ) i (vTOf vT))
  hptsU : ∀ (ζ : VF.K3) (ck : ι × Fin r), ∃ pt ∈ (openPts XI ζ).toList, toKV pt = A.pt ck.1 ck.2 (toKV ζ)
  hRVU : ∀ (c0 : Block Φ KC 0) (c1 : Block Φ KC 1) (c2 : Block Φ KC 2) (c3 : Block Φ KC 3) (vT : Array (Array VF.K3)) (vQ : Array VF.K3),
    VShape XI vT vQ →
    PR (slotsAt XI (ds.2.1.encC c0) (ds.2.2.1.encC c1)) (pubAt XI vT) →
    RestV (ds.1.decM []) (ds.2.2.2.2.2.1.decM (deepMsg vT vQ)) (chiOfBlocks c0 c1 c2 c3)
  hH : P.H = (Finset.range XI.hN).image (fun i => psiV XI.hShift * psiV XI.hGen ^ i)
  he : P.e = 3
  hnq : XI.nq = P.nq
  hcw : ∀ j : Fin P.nq, toKV VF.K3.gen ^ (j.1 % 3) = P.cw j


variable (pp : PATH) (dY : List ℕ → Dg) (ds : MDec (MC)) (ω0 : Op) (vTOf : Array (Array VF.K3) → ι × Fin r → KC)

/-- **`hα`, `hζ`, `hlen`, `hdag`, `hH`, `he`, `hnq`, `hcw`, `hQ` of `DeepLinkC`**, from `UniLinks`, `chalsOf = fs_chal_dec` and the `Mfin` message -/
theorem deepLinkC_of' (U : UniLinks' XI H FS zF π hv P A R0 Rest RestV e I0 I Ifin d Dg enc md L PR dY ds vTOf) (hok : FlatOk XI H FS zF π)
    (hch : ChalsDec XI H FS zF π hv P A R0 Rest RestV e I0 I Ifin d Dg enc md L Op dY ds ω0 pp)
    (hm5 : pp.2.2.2.2.2.2.2.2.2.2.1 = ds.2.2.2.2.2.1.decM (deepMsg π.vT π.vQ)) :
    DeepLinkC XI H FS zF π P A (CHI pp) ((CHI pp) P.a) ((CHI pp) P.z) (FINM pp).2.1 (FINM pp).2.2 := by
  have hc := allCanon_of_flatOk XI H FS zF π hok
  have hsh := vshape_of_flat XI H FS zF π hok
  have e3 : (encPathD _ (mDecs dY (MC) ds ω0) pp).getD 3 [] = ds.2.2.2.1.encC (pp.2.2.2.2.2.2.2.1 : Block Φ KC 2) := rfl
  have e4 : (encPathD _ (mDecs dY (MC) ds ω0) pp).getD 4 [] = ds.2.2.2.2.1.encC (pp.2.2.2.2.2.2.2.2.2.1 : Block Φ KC 3) := rfl
  have hslots := slots_link XI H FS zF π hv P A R0 Rest RestV e I0 I Ifin d Dg enc md L Op dY ds ω0 pp hch
  have halpha : toKV (alphaOf XI FS zF π) = (CHI pp) P.a := by
    refine Eq.trans ?_ (chi_at2 (hv := hv) (decode := decode) (pp := pp) (i := P.a) (h := U.hPa)).symm
    refine Eq.trans ?_ (U.hαC (pp.2.2.2.2.2.2.2.1 : Block Φ KC 2))
    unfold alphaOf
    rw [hch 3 (by omega) (by simp [roundNl]), e3]
  have hzeta : toKV (zetaOf XI FS zF π) = (CHI pp) P.z := by
    refine Eq.trans ?_ (chi_at3 (hv := hv) (decode := decode) (pp := pp) (i := P.z) (h := U.hPz)).symm
    refine Eq.trans ?_ (U.hζC (pp.2.2.2.2.2.2.2.2.2.1 : Block Φ KC 3))
    unfold zetaOf
    rw [hch 4 (by omega) (by simp [roundNl]), e4]
  have hlen : (termsOfK XI FS zF π).length = P.ns := by rw [termsOfK_eq]; exact U.hlenU _ _ _
  have hVTq : (FINM pp).2.1 = vTOf π.vT := by rw [finM_eq (hv := hv) (decode := decode), hm5]; exact U.hVT _ _ hsh
  refine ⟨halpha, hzeta, hlen, ?_, U.hH, U.he, U.hnq, U.hcw, ?_⟩
  · intro i
    have hcan : CanonIn (slotsOf XI FS zF π) (zetaOf XI FS zF π) π.vT :=
      ⟨slotsOf_canon XI H FS zF π hok, canon3_zetaOf XI FS zF π hc.chal, (flatOk_limbs XI H FS zF π hok).1⟩
    rw [hslots] at hcan
    have h := U.hdagU (pp.2.2.2.1 : Block Φ KC 0) (pp.2.2.2.2.2.1 : Block Φ KC 1) (pp.2.2.2.2.2.2.2.1 : Block Φ KC 2)
      (pp.2.2.2.2.2.2.2.2.2.1 : Block Φ KC 3) (zetaOf XI FS zF π) π.vT hcan (Fin.cast hlen i)
    rw [← hslots, ← termsOfK_eq] at h
    rw [List.getElem?_eq_getElem (by simp)] at h
    have h' := Option.some.inj h
    rw [List.get_eq_getElem]
    simp only [Fin.val_cast] at h'
    rw [h', hVTq, ← hzeta, chi_eq (hv := hv) (decode := decode)]
    rfl
  · intro j
    rw [finM_eq (hv := hv) (decode := decode), hm5]
    exact (U.hQU _ _ hsh j).symm

/-- `hpts` of `ClosedLinksL` -/
theorem hpts_of' (U : UniLinks' XI H FS zF π hv P A R0 Rest RestV e I0 I Ifin d Dg enc md L PR dY ds vTOf)
    (D : DeepLinkC XI H FS zF π P A (CHI pp) ((CHI pp) P.a) ((CHI pp) P.z) (FINM pp).2.1 (FINM pp).2.2) :
    ∀ ck : ι × Fin r, ∃ pt ∈ (openPts XI (zetaOf XI FS zF π)).toList, toKV pt = A.pt ck.1 ck.2 ((CHI pp) P.z) := by
  intro ck
  obtain ⟨pt, hm, h⟩ := U.hptsU (zetaOf XI FS zF π) ck
  exact ⟨pt, hm, by rw [h, D.hζ]⟩

/-- `hRV` of `ClosedLinksL` -/
theorem hRV_of' (U : UniLinks' XI H FS zF π hv P A R0 Rest RestV e I0 I Ifin d Dg enc md L PR dY ds vTOf) (hok : FlatOk XI H FS zF π)
    (hch : ChalsDec XI H FS zF π hv P A R0 Rest RestV e I0 I Ifin d Dg enc md L Op dY ds ω0 pp)
    (hm0 : pp.1 = ds.1.decM [])
    (hm5 : pp.2.2.2.2.2.2.2.2.2.2.1 = ds.2.2.2.2.2.1.decM (deepMsg π.vT π.vQ)) :
    PR (slotsOf XI FS zF π) (pubOfProof XI π) →
      RestV (MA.fstB Dg (RM) (BM) (q0P P A R0 Rest RestV e I0 I Ifin 4 s1 d XI.l Dg enc md L Op decode pp)).1
        (FINM pp) (CHI pp) := by
  intro hP
  have hsh := vshape_of_flat XI H FS zF π hok
  rw [slots_link XI H FS zF π hv P A R0 Rest RestV e I0 I Ifin d Dg enc md L Op dY ds ω0 pp hch, pubOfProof_eq] at hP
  have h := U.hRVU (pp.2.2.2.1 : Block Φ KC 0) (pp.2.2.2.2.2.1 : Block Φ KC 1) (pp.2.2.2.2.2.2.2.1 : Block Φ KC 2)
    (pp.2.2.2.2.2.2.2.2.2.1 : Block Φ KC 3) π.vT π.vQ hsh hP
  rw [← hm5] at h
  rw [← hm0] at h
  exact h
/-- `hxs` with the query codec fact stated at the ONE decoder tuple of the proof ('s `XsCodec` quantified over all tuples) -/
theorem hxs_of'     (dY : List ℕ → Dg) (ds : MDec (MC)) (ω0 : Op) (pp : PATH)
    (hX : ∀ (q : (protocol (compiledRoundsK Dg Op (Fri.friMerkleMask s1 d XI.l L Dg enc 0 XI.k (by omega)))).tree.ExecutionPath)
      (j : Fin XI.l), (Fri.XsOf s1 d XI.l L Dg enc Op 0 XI.k (by omega) q j).val =
        homV.ψ XI.dShift * homV.ψ XI.dGen ^ ((lastEnc XI H FS zF π hv d Dg enc L Op 0 XI.k (by omega) (sndD (RM) (BM) ds).2.2 q)[j.1]! % 2 ^ XI.nD))
    (hok : FlatOk XI H FS zF π)
    (hch : (chalsOf XI FS zF π)[8 + XI.k]! = (encPathD _ (mDecs dY (MC) ds ω0) pp).getD (8 + XI.k) []) (j : Fin XI.l) :
    (xsC P A R0 Rest RestV e I0 I Ifin 4 s1 d XI.l Dg enc md L Op pp j).val =
      homV.ψ XI.dShift * homV.ψ XI.dGen ^ π.pos[j.1]! := by
  rw [pos_get XI H FS zF π hok j, hch, enc_query (hv := hv) (pp := pp) ..]
  exact hX _ j

theorem rapLinks_of_uni' (U : UniLinks' XI H FS zF π hv P A R0 Rest RestV e I0 I Ifin d Dg enc md L PR dY ds vTOf) (hok : FlatOk XI H FS zF π)
    (hX : ∀ (q : (protocol (compiledRoundsK Dg Op (Fri.friMerkleMask s1 d XI.l L Dg enc 0 XI.k (by omega)))).tree.ExecutionPath)
      (j : Fin XI.l), (Fri.XsOf s1 d XI.l L Dg enc Op 0 XI.k (by omega) q j).val =
        homV.ψ XI.dShift * homV.ψ XI.dGen ^ ((lastEnc XI H FS zF π hv d Dg enc L Op 0 XI.k (by omega) (sndD (RM) (BM) ds).2.2 q)[j.1]! % 2 ^ XI.nD))
    (hch : ChalsDec XI H FS zF π hv P A R0 Rest RestV e I0 I Ifin d Dg enc md L Op dY ds ω0 pp)
    (hm0 : pp.1 = ds.1.decM [])
    (hm5 : pp.2.2.2.2.2.2.2.2.2.2.1 = ds.2.2.2.2.2.1.decM (deepMsg π.vT π.vQ)) :
    RapLinks XI H FS zF π hv P A R0 Rest RestV e I0 I Ifin d Dg enc md L Op PR decode pp := by
  have D := deepLinkC_of' XI H FS zF π hv P A R0 Rest RestV e I0 I Ifin d Dg enc md L Op PR decode pp dY ds ω0 vTOf U hok hch hm5
  exact ⟨fun j => hxs_of' XI H FS zF π hv P A R0 Rest RestV e I0 I Ifin d Dg enc md L Op dY ds ω0 pp hX hok
      (hch _ (by omega) (roundNl_query XI H FS zF π hok)) j,
    D, hpts_of' XI H FS zF π hv P A R0 Rest RestV e I0 I Ifin d Dg enc md L Op PR decode pp dY ds vTOf U D,
    hRV_of' XI H FS zF π hv P A R0 Rest RestV e I0 I Ifin d Dg enc md L Op PR decode pp dY ds ω0 vTOf U hok hch hm0 hm5⟩

end UL

end PRE

/-! ## the pointwise soundness `verifyFlat_sound_tab` -/

theorem roundNl_fri_ne (XI : ExecInst) (hl : 1 ≤ XI.l) (t : ℕ) (ht : t < XI.k + 2) : roundNl XI (7 + t) ≠ 0 := by
  unfold roundNl
  by_cases h : t ≤ XI.k
  · have e1 : (7 + t == 1) = false := by simp <;> omega
    have e2 : (7 + t == 2) = false := by simp <;> omega
    have e3 : (7 + t == 3) = false := by simp <;> omega
    have e4 : (7 + t == 4) = false := by simp <;> omega
    have e5 : (7 + t == 5) = false := by simp <;> omega
    have e6 : (7 + t == 6) = false := by simp <;> omega
    simp only [e1, e2, e3, e4, e5, e6, Bool.false_or, Bool.false_eq_true, ite_false]
    have : (decide (7 + t ≥ 7) && decide (7 + t ≤ 7 + XI.k)) = true := by simp [h]
    simp [h]
  · have ht' : t = XI.k + 1 := by omega
    subst ht'
    have e1 : (7 + (XI.k + 1) == 1) = false := by simp <;> omega
    have e2 : (7 + (XI.k + 1) == 2) = false := by simp <;> omega
    have e3 : (7 + (XI.k + 1) == 3) = false := by simp <;> omega
    have e4 : (7 + (XI.k + 1) == 4) = false := by simp <;> omega
    have e5 : (7 + (XI.k + 1) == 5) = false := by simp <;> omega
    have e6 : (7 + (XI.k + 1) == 6) = false := by simp <;> omega
    have e7 : (7 + (XI.k + 1) == 8 + XI.k) = true := by simp; omega
    simp only [e1, e2, e3, e4, e5, e6, Bool.false_or, Bool.false_eq_true, ite_false]
    have : (decide (7 + (XI.k + 1) ≥ 7) && decide (7 + (XI.k + 1) ≤ 7 + XI.k)) = false := by simp
    simp [this, e7]
    omega

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

/-- the path of the embedded messages under the table -/
noncomputable def EP {Statement Salt : Type} (ds : MDec (MC)) (z : Statement × Salt)
    (gg : (k : Key (Statement × Salt) PUnit (compiledRoundsK DgJ8 (OPN) (MC))) → k.Challenge) (π : FlatProof) :
    (protocol (compiledRoundsK DgJ8 (OPN) (MC))).tree.ExecutionPath :=
  pathOf z _ gg (embedMsgs dgOf (MC) ds (openAllOf (merkleSkels (MC)) (flatTrees (XI170 XI0) π)) (msgsOf (XI170 XI0) π).toList)

/-- **`verifyFlat_sound_tab`** (generic in the flat views `H`, `FS` of the table; the residual codec facts are hypotheses). -/
theorem verifyFlat_sound_tab_gen
    {Statement Salt : Type} [DecidableEq Statement] [DecidableEq Salt]
    (encZ : Statement × Salt → List ℕ) (decZ : List ℕ → Statement × Salt) (hz : ∀ x, decZ (encZ x) = x)
    (z : Statement × Salt)
    (g : (dd : NQuery (merkleSkels (MC)) ⊕ Key (Statement × Salt) PUnit (compiledRoundsK DgJ8 (OPN) (MC))) →
      succinctRange DgJ8 (OPN) (NQuery (merkleSkels (MC))) Statement Salt (MC) dd)
    (π : FlatProof) (H : HFn) (FS : FSFn) (ds : MDec (MC)) (ω0 : OPN)
    (da : MDec (RM)) (dsb : RDec (batchRound KC)) (dsm : MDec (friMask s1 d (XI170 XI0).l L DgJ8 enc))
    (hds : ds = mdAppend (RM) (BM) da (dsb, dsm))
    (hH : H = Hof (merkleSkels (MC)) (fun q => g (.inl q)))
    (hFS : ∀ x n, FS x n = FSdec (compiledRoundsK DgJ8 (OPN) (MC)) (mDecs dgOf (MC) ds ω0) decZ (fun k => g (.inr k)) x)
    (vTOf : Array (Array VF.K3) → ι × Fin r → KC)
    (encB : B ↪ DgJ8) (rk : ∀ r, {c : ι ⊕ Fin P.nq // P.colRoundX c = r} ≃ Fin (Wb (XI170 XI0) r))
    (hn1 : 1 ≤ (XI170 XI0).nD) (hmd : md = mdX (XI170 XI0) hn1 P.colRoundX rk encB) (hL : L = LX (XI170 XI0) hn32) (hPS : PubSound (XI170 XI0) PR)
    (hv : verifyFlat (XI170 XI0) H FS (encZ z) π = true)
    (U : UniLinks' (XI170 XI0) H FS (encZ z) π hv P A R0 Rest RestV e I0 I Ifin d DgJ8 enc md L PR dgOf ds vTOf)
    (hX : ∀ (q : (protocol (compiledRoundsK DgJ8 (OPN) (friMerkleMask s1 d (XI170 XI0).l L DgJ8 enc 0 (XI170 XI0).k (by omega)))).tree.ExecutionPath)
      (j : Fin (XI170 XI0).l), (XsOf s1 d (XI170 XI0).l L DgJ8 enc (OPN) 0 (XI170 XI0).k (by omega) q j).val =
        homV.ψ (XI170 XI0).dShift * homV.ψ (XI170 XI0).dGen ^ ((E2ELR.lastEnc (XI170 XI0) H FS (encZ z) π hv d DgJ8 enc L (OPN) 0 (XI170 XI0).k (by omega) (E2ELR.sndD (RM) (BM) ds).2.2 q)[j.1]! % 2 ^ (XI170 XI0).nD))
    (hcod0 : ∀ x, cast (foldChallenge_type (ω := ωS) s1 (XI170 XI0).l ⟨0, by omega⟩)
      (xp (a := ⟨0, by have := friLength (k := (XI170 XI0).k); omega⟩) (b := (foldChallenge (ω := ωS) s1 (XI170 XI0).l ⟨0, by omega⟩).val)
        (Fin.ext (by simp only [foldChallenge_val])) (dsm.1.decC x)) = toKV (VF.K3.ofLimbs x))
    (hcod : E2EFri.CodOK s1 d (XI170 XI0).l L DgJ8 enc (fun x => toKV (VF.K3.ofLimbs x)) 0 (XI170 XI0).k (by omega) dsm.2)
    (hvalF : E2EFri.ValF s1 d (XI170 XI0).l L DgJ8 enc (E2EFri.lvK (XI170 XI0) π) 0 (XI170 XI0).k (by omega)
      (MA.sndOpen (RM) (BM) (openAllOf (merkleSkels (MC)) (flatTrees (XI170 XI0) π))))
    (hPdec : ∀ y, (E2EFri.finPolyOf s1 d (XI170 XI0).l L DgJ8 enc (OPN) 0 (XI170 XI0).k (by omega)
      (MA.sndK DgJ8 (OPN) (RM) (BM) (EP XI0 hn32 P A R0 Rest RestV e I0 I Ifin d enc md L ds z (fun k => g (.inr k)) π)).2.2.2.2).eval y =
      hornerF (fun j => homV.φ π.pfinal[j]!) π.pfinal.size y)
    (hW0 : E2EFri.W0Link (XI170 XI0) H FS (encZ z) π hv P A R0 Rest RestV e I0 I Ifin 4 d GG DgJ8 enc md L (OPN) id z
      (EP XI0 hn32 P A R0 Rest RestV e I0 I Ifin d enc md L ds z (fun k => g (.inr k)) π)) :
    ∃ p, tabEval (tabK g) (succinctVerifyK (Query := NQuery (merkleSkels (MC))) (trueGuards _)
        (merkleCheck (merkleSkels (MC)) (idModel (merkleSkels (MC))) id)
        (cLocal P A R0 Rest RestV e I0 I Ifin 4 s1 d (XI170 XI0).l GG DgJ8 enc md L hdom (OPN) id) z
        (embedMsgs dgOf (MC) ds (openAllOf (merkleSkels (MC)) (flatTrees (XI170 XI0) π)) (msgsOf (XI170 XI0) π).toList)) = some (some p) := by
  classical
  have hok := (verifyFlat_iff (XI170 XI0) H FS (encZ z) π).mp hv
  have hr : π.roots.size = 4 + (XI170 XI0).k := by
    obtain ⟨_, _, _, _, h5, _⟩ := hok
    simp only [Bool.and_eq_true, beq_iff_eq] at h5
    exact h5.1.1
  have hroots : pathRootsK DgJ8 (OPN) (MC)
      (pathOf z (compiledRoundsK DgJ8 (OPN) (MC)) (fun k => g (.inr k))
        (embedMsgs dgOf (MC) ds (openAllOf (merkleSkels (MC)) (flatTrees (XI170 XI0) π)) (msgsOf (XI170 XI0) π).toList)) =
      (rootsOf π, openAllOf (merkleSkels (MC)) (flatTrees (XI170 XI0) π)) := by
    rw [pathRootsK_embed dgOf z (MC) ds _ _ (fun k => g (.inr k)), merkleMsgs_msC (XI170 XI0) H FS (encZ z) π hv P A R0 Rest RestV e I0 I Ifin 4 d enc md L rfl hr]
  have hlist := hsk_list (S := KC) (XI170 XI0) H FS (encZ z) π hv P A R0 Rest RestV e I0 I Ifin 4 d enc md L encB rk hmd hL rfl
  have hlen : (merkleSkels (MC)).length = 4 + (XI170 XI0).k := by rw [hlist]; simp
  have hsk : ∀ j (hj : j < (merkleSkels (MC)).length), (merkleSkels (MC)).get ⟨j, hj⟩ = skelFlat (XI170 XI0) j := by
    intro j hj; simp [hlist]
  have hok' : FlatOk (XI170 XI0) (Hof (merkleSkels (MC)) (fun q => g (.inl q))) FS (encZ z) π := by rw [← hH]; exact hok
  have hMerkle : tabEval (spec := NQuery (merkleSkels (MC)) →ₒ DgJ8) (fun q => some (g (.inl q)))
      (merkleCheck (merkleSkels (MC)) (idModel (merkleSkels (MC))) id (rootsOf π) (openAllOf (merkleSkels (MC)) (flatTrees (XI170 XI0) π))) = some true :=
    merkle_embed (XI170 XI0) FS (encZ z) π (merkleSkels (MC)) (fun q => g (.inl q)) hok' hlen hsk
  have hmsd := embedMsgs_dec dgOf (MC) ds (openAllOf (merkleSkels (MC)) (flatTrees (XI170 XI0) π)) ω0 (msgsOf (XI170 XI0) π).toList
    (by rw [length_msgsOf (XI170 XI0) π hr, length_msC (XI170 XI0) H FS (encZ z) π hv P A R0 Rest RestV e I0 I Ifin 4 d enc md L rfl])
  have hlenm : (msgsOf (XI170 XI0) π).size = 9 + (XI170 XI0).k := by
    have := length_msgsOf (XI170 XI0) π hr
    simpa using this
  have hch : E2ELR.ChalsDec (XI170 XI0) H FS (encZ z) π hv P A R0 Rest RestV e I0 I Ifin d DgJ8 enc md L (OPN) dgOf ds ω0
      (pathOf z (compiledRoundsK DgJ8 (OPN) (MC)) (fun k => g (.inr k))
        (embedMsgs dgOf (MC) ds (openAllOf (merkleSkels (MC)) (flatTrees (XI170 XI0) π)) (msgsOf (XI170 XI0) π).toList)) := by
    intro i hi hnl
    exact chalsOf_dec (XI170 XI0) π encZ decZ hz _ (mDecs dgOf (MC) ds ω0) (fun k => g (.inr k)) z _ hmsd FS hFS i
      (by omega) hnl
  obtain ⟨hm0, hm5⟩ := E2ELR.embed_msgs (XI170 XI0) H FS (encZ z) π hv P A R0 Rest RestV e I0 I Ifin d DgJ8 enc md L (OPN) dgOf ds (openAllOf (merkleSkels (MC)) (flatTrees (XI170 XI0) π)) z
    (fun k => g (.inr k))
  have hRap := rapLinks_of_uni' (XI170 XI0) H FS (encZ z) π hv P A R0 Rest RestV e I0 I Ifin d DgJ8 enc md L (OPN) PR id _ dgOf ds ω0 vTOf U hok hX
    hch hm0 hm5
  have hH' : H = Hof (merkleSkels (MC)) (fun q => g (.inl q)) := hH
  have hsel : SelLinkC (XI170 XI0) H FS (encZ z) π hv P A R0 Rest RestV e I0 I Ifin 4 d DgJ8 enc md L
      (id (pathRootsK DgJ8 (OPN) (MC) (pathOf z (compiledRoundsK DgJ8 (OPN) (MC)) (fun k => g (.inr k))
        (embedMsgs dgOf (MC) ds (openAllOf (merkleSkels (MC)) (flatTrees (XI170 XI0) π)) (msgsOf (XI170 XI0) π).toList))).2) := by
    rw [hroots]
    exact selLinkC_embed (XI170 XI0) H FS (encZ z) π hv P A R0 Rest RestV e I0 I Ifin 4 d enc md L encB rk hmd hL rfl
      (fun q => g (.inl q)) hH'
  have hl1 : 1 ≤ (XI170 XI0).l := by
    obtain ⟨_, _, h3, _⟩ := hok
    simp only [Bool.and_eq_true, decide_eq_true_eq, ge_iff_le] at h3
    exact h3.2
  have hchF : ∀ t, t < (XI170 XI0).k + 2 → (encPathD (compiledRoundsK DgJ8 (OPN) (friMask s1 d (XI170 XI0).l L DgJ8 enc))
      (mDecs dgOf (friMask s1 d (XI170 XI0).l L DgJ8 enc) dsm ω0)
      (MA.sndK DgJ8 (OPN) (RM) (BM) (pathOf z (compiledRoundsK DgJ8 (OPN) (MC)) (fun k => g (.inr k))
        (embedMsgs dgOf (MC) ds (openAllOf (merkleSkels (MC)) (flatTrees (XI170 XI0) π)) (msgsOf (XI170 XI0) π).toList))).2.2).getD t [] =
      E2EFri.chV (XI170 XI0) FS (encZ z) π (7 + t) := by
    intro t ht
    subst hds
    have h1 := E2EFri.encPathD_append_getD dgOf ω0 (RM) (BM) da (dsb, dsm)
      (pathOf z (compiledRoundsK DgJ8 (OPN) (MC)) (fun k => g (.inr k))
        (embedMsgs dgOf (MC) (mdAppend (RM) (BM) da (dsb, dsm)) (openAllOf (merkleSkels (MC)) (flatTrees (XI170 XI0) π)) (msgsOf (XI170 XI0) π).toList)) (t + 1)
    have h6 : (RM).length = 6 := rfl
    rw [h6, show 6 + (t + 1) = 7 + t by omega] at h1
    have h2 := hch (7 + t) (by omega) (roundNl_fri_ne (XI170 XI0) hl1 t ht)
    unfold E2EFri.chV
    rw [h2, h1]
    rfl
  have hF := E2EFri.friLinkAt_of_flat (XI170 XI0) H FS (encZ z) π hv P A R0 Rest RestV e I0 I Ifin 4 d GG DgJ8 enc md L (OPN) hok hL id z _
    hRap.hxs hsel.2 (by rw [hroots]; exact hvalF) dgOf ω0 dsm hchF hcod0 hcod hPdec hW0
  have hLs : ClosedLinksL (XI170 XI0) H FS (encZ z) π hv P A R0 Rest RestV e I0 I Ifin 4 d GG DgJ8 enc md L (OPN) id z
      (pathOf z (compiledRoundsK DgJ8 (OPN) (MC)) (fun k => g (.inr k))
        (embedMsgs dgOf (MC) ds (openAllOf (merkleSkels (MC)) (flatTrees (XI170 XI0) π)) (msgsOf (XI170 XI0) π).toList))
      PR := ⟨hsel, hRap.hxs, hRap.hD, hRap.hpts, hRap.hRV, hF⟩
  have hsound := verifyFlat_sound'' (XI170 XI0) H FS (encZ z) π hv P A R0 Rest RestV e I0 I Ifin 4 d GG DgJ8 enc md L hdom (OPN) encB rk hmd hL id z _ PR hPS hLs
  have hp : pathOfG (fun key => g (.inr key)) (compiledRoundsK DgJ8 (OPN) (MC)) z
      (embedMsgs dgOf (MC) ds (openAllOf (merkleSkels (MC)) (flatTrees (XI170 XI0) π)) (msgsOf (XI170 XI0) π).toList) id (fun _ => rfl) =
      pathOf z (compiledRoundsK DgJ8 (OPN) (MC)) (fun k => g (.inr k))
        (embedMsgs dgOf (MC) ds (openAllOf (merkleSkels (MC)) (flatTrees (XI170 XI0) π)) (msgsOf (XI170 XI0) π).toList) :=
    pathOfG_eq_pathOf (fun key => g (.inr key)) z _ _ id (fun _ => rfl)
  refine ⟨_, tabEval_succinctVerifyK g _ _ z _ _ hp ?_ hsound.2.1⟩
  rw [hroots]
  exact hMerkle

/-! ## `exec_e2e` -/

/-- the flat hash view of a table (node queries) -/
noncomputable abbrev HT {Statement Salt : Type}
    (g : (dd : NQuery (merkleSkels (MC)) ⊕ Key (Statement × Salt) PUnit (compiledRoundsK DgJ8 (OPN) (MC))) →
      succinctRange DgJ8 (OPN) (NQuery (merkleSkels (MC))) Statement Salt (MC) dd) : HFn :=
  Hof (merkleSkels (MC)) (fun q => g (.inl q))

/-- the flat Fiat-Shamir view of a table (the decoders `ds`; the opening round's decoder is never read, `ω0` is a fixed dummy) -/
noncomputable abbrev FST {Statement Salt : Type} (decZ : List ℕ → Statement × Salt) (ds : MDec (MC))
    (g : (dd : NQuery (merkleSkels (MC)) ⊕ Key (Statement × Salt) PUnit (compiledRoundsK DgJ8 (OPN) (MC))) →
      succinctRange DgJ8 (OPN) (NQuery (merkleSkels (MC))) Statement Salt (MC) dd) : FSFn :=
  fun x _ => FSdec (compiledRoundsK DgJ8 (OPN) (MC)) (mDecs dgOf (MC) ds (openAllOf (merkleSkels (MC)) []) ) decZ (fun k => g (.inr k)) x

/-- **acceptance of the flat verifier on the flat views of the table** -/
noncomputable def AccF {Statement Salt : Type} (encZ : Statement × Salt → List ℕ) (decZ : List ℕ → Statement × Salt) (ds : MDec (MC))
    (g : (dd : NQuery (merkleSkels (MC)) ⊕ Key (Statement × Salt) PUnit (compiledRoundsK DgJ8 (OPN) (MC))) →
      succinctRange DgJ8 (OPN) (NQuery (merkleSkels (MC))) Statement Salt (MC) dd)
    (z : Statement × Salt) (π : FlatProof) : Prop :=
  verifyFlat (XI170 XI0) (HT XI0 hn32 P A R0 Rest RestV e I0 I Ifin d enc md L g) (FST XI0 hn32 P A R0 Rest RestV e I0 I Ifin d enc md L decZ ds g) (encZ z) π = true


/-- the instance-level codec/alignment facts left to the J-8 instance, each quantified over the accepted flat proofs (the
quantification only supplies the verifier's proof `hv` that fixes the audited domain; the content of `hU`, `hX` is π- and g-free) -/
structure Resid {Statement Salt : Type} (encZ : Statement × Salt → List ℕ) (decZ : List ℕ → Statement × Salt)
    (da : MDec (RM)) (dsb : RDec (batchRound KC)) (dsm : MDec (friMask s1 d (XI170 XI0).l L DgJ8 enc))
    (vTOf : Array (Array VF.K3) → ι × Fin r → KC) : Prop where
  hU : ∀ g z π (hv : AccF XI0 hn32 P A R0 Rest RestV e I0 I Ifin d enc md L encZ decZ (mdAppend (RM) (BM) da (dsb, dsm)) g z π),
    UniLinks' (XI170 XI0) (HT XI0 hn32 P A R0 Rest RestV e I0 I Ifin d enc md L g)
      (FST XI0 hn32 P A R0 Rest RestV e I0 I Ifin d enc md L decZ (mdAppend (RM) (BM) da (dsb, dsm)) g) (encZ z) π hv
      P A R0 Rest RestV e I0 I Ifin d DgJ8 enc md L PR dgOf (mdAppend (RM) (BM) da (dsb, dsm)) vTOf
  hX : ∀ g z π (hv : AccF XI0 hn32 P A R0 Rest RestV e I0 I Ifin d enc md L encZ decZ (mdAppend (RM) (BM) da (dsb, dsm)) g z π),
    ∀ (q : (protocol (compiledRoundsK DgJ8 (OPN) (friMerkleMask s1 d (XI170 XI0).l L DgJ8 enc 0 (XI170 XI0).k (by omega)))).tree.ExecutionPath)
      (j : Fin (XI170 XI0).l), (XsOf s1 d (XI170 XI0).l L DgJ8 enc (OPN) 0 (XI170 XI0).k (by omega) q j).val =
        homV.ψ (XI170 XI0).dShift * homV.ψ (XI170 XI0).dGen ^ ((E2ELR.lastEnc (XI170 XI0) (HT XI0 hn32 P A R0 Rest RestV e I0 I Ifin d enc md L g)
          (FST XI0 hn32 P A R0 Rest RestV e I0 I Ifin d enc md L decZ (mdAppend (RM) (BM) da (dsb, dsm)) g) (encZ z) π hv d DgJ8 enc L (OPN) 0 (XI170 XI0).k (by omega)
          (E2ELR.sndD (RM) (BM) (mdAppend (RM) (BM) da (dsb, dsm))).2.2 q)[j.1]! % 2 ^ (XI170 XI0).nD)
  hcod0 : ∀ x, cast (foldChallenge_type (ω := ωS) s1 (XI170 XI0).l ⟨0, by omega⟩)
      (xp (a := ⟨0, by have := friLength (k := (XI170 XI0).k); omega⟩) (b := (foldChallenge (ω := ωS) s1 (XI170 XI0).l ⟨0, by omega⟩).val)
        (Fin.ext (by simp only [foldChallenge_val])) (dsm.1.decC x)) = toKV (VF.K3.ofLimbs x)
  hcod : E2EFri.CodOK s1 d (XI170 XI0).l L DgJ8 enc (fun x => toKV (VF.K3.ofLimbs x)) 0 (XI170 XI0).k (by omega) dsm.2
  hvalF : ∀ g z π, AccF XI0 hn32 P A R0 Rest RestV e I0 I Ifin d enc md L encZ decZ (mdAppend (RM) (BM) da (dsb, dsm)) g z π →
    E2EFri.ValF s1 d (XI170 XI0).l L DgJ8 enc (E2EFri.lvK (XI170 XI0) π) 0 (XI170 XI0).k (by omega)
      (MA.sndOpen (RM) (BM) (openAllOf (merkleSkels (MC)) (flatTrees (XI170 XI0) π)))
  hPdec : ∀ g z π, AccF XI0 hn32 P A R0 Rest RestV e I0 I Ifin d enc md L encZ decZ (mdAppend (RM) (BM) da (dsb, dsm)) g z π →
    ∀ y, (E2EFri.finPolyOf s1 d (XI170 XI0).l L DgJ8 enc (OPN) 0 (XI170 XI0).k (by omega)
      (MA.sndK DgJ8 (OPN) (RM) (BM) (EP XI0 hn32 P A R0 Rest RestV e I0 I Ifin d enc md L (mdAppend (RM) (BM) da (dsb, dsm)) z (fun k => g (.inr k)) π)).2.2.2.2).eval y =
      hornerF (fun j => homV.φ π.pfinal[j]!) π.pfinal.size y
  hW0 : ∀ g z π (hv : AccF XI0 hn32 P A R0 Rest RestV e I0 I Ifin d enc md L encZ decZ (mdAppend (RM) (BM) da (dsb, dsm)) g z π),
    E2EFri.W0Link (XI170 XI0) (HT XI0 hn32 P A R0 Rest RestV e I0 I Ifin d enc md L g)
      (FST XI0 hn32 P A R0 Rest RestV e I0 I Ifin d enc md L decZ (mdAppend (RM) (BM) da (dsb, dsm)) g) (encZ z) π hv P A R0 Rest RestV e I0 I Ifin 4 d GG DgJ8 enc md L (OPN) id z
      (EP XI0 hn32 P A R0 Rest RestV e I0 I Ifin d enc md L (mdAppend (RM) (BM) da (dsb, dsm)) z (fun k => g (.inr k)) π)

/-- **`verifyFlat_sound_tab`**: the flat verifier accepting on the flat views of a table forces the audited succinct verifier (accept-all
guards, identity node model, `decode = id`) to return a path on the embedded messages. -/
theorem verifyFlat_sound_tab {Statement Salt : Type} [DecidableEq Statement] [DecidableEq Salt]
    (encZ : Statement × Salt → List ℕ) (decZ : List ℕ → Statement × Salt) (hz : ∀ x, decZ (encZ x) = x)
    (da : MDec (RM)) (dsb : RDec (batchRound KC)) (dsm : MDec (friMask s1 d (XI170 XI0).l L DgJ8 enc))
    (vTOf : Array (Array VF.K3) → ι × Fin r → KC)
    (encB : B ↪ DgJ8) (rk : ∀ r, {c : ι ⊕ Fin P.nq // P.colRoundX c = r} ≃ Fin (Wb (XI170 XI0) r))
    (hn1 : 1 ≤ (XI170 XI0).nD) (hmd : md = mdX (XI170 XI0) hn1 P.colRoundX rk encB) (hL : L = LX (XI170 XI0) hn32) (hPS : PubSound (XI170 XI0) PR)
    (R : Resid XI0 hn32 P A R0 Rest RestV e I0 I Ifin d enc md L PR encZ decZ da dsb dsm vTOf)
    (g : (dd : NQuery (merkleSkels (MC)) ⊕ Key (Statement × Salt) PUnit (compiledRoundsK DgJ8 (OPN) (MC))) →
      succinctRange DgJ8 (OPN) (NQuery (merkleSkels (MC))) Statement Salt (MC) dd)
    (z : Statement × Salt) (π : FlatProof)
    (hacc : AccF XI0 hn32 P A R0 Rest RestV e I0 I Ifin d enc md L encZ decZ (mdAppend (RM) (BM) da (dsb, dsm)) g z π) :
    ∃ p, tabEval (tabK g) (succinctVerifyK (Query := NQuery (merkleSkels (MC))) (trueGuards _)
        (merkleCheck (merkleSkels (MC)) (idModel (merkleSkels (MC))) id)
        (cLocal P A R0 Rest RestV e I0 I Ifin 4 s1 d (XI170 XI0).l GG DgJ8 enc md L hdom (OPN) id) z
        (embedMsgs dgOf (MC) (mdAppend (RM) (BM) da (dsb, dsm)) (openAllOf (merkleSkels (MC)) (flatTrees (XI170 XI0) π))
          (msgsOf (XI170 XI0) π).toList)) = some (some p) :=
  verifyFlat_sound_tab_gen XI0 hn32 P A R0 Rest RestV e I0 I Ifin d enc md L hdom PR encZ decZ hz z g π
    (HT XI0 hn32 P A R0 Rest RestV e I0 I Ifin d enc md L g) (FST XI0 hn32 P A R0 Rest RestV e I0 I Ifin d enc md L decZ (mdAppend (RM) (BM) da (dsb, dsm)) g)
    (mdAppend (RM) (BM) da (dsb, dsm)) (openAllOf (merkleSkels (MC)) []) da dsb dsm rfl rfl (fun _ _ => rfl) vTOf encB rk hn1 hmd hL hPS
    hacc (R.hU g z π hacc) (R.hX g z π hacc) (R.hcod0) (R.hcod) (R.hvalF g z π hacc) (R.hPdec g z π hacc) (R.hW0 g z π hacc)

set_option hygiene false in
local notation "EMB" => fun (da : MDec (RM)) (dsb : RDec (batchRound KC)) (dsm : MDec (friMask s1 d (XI170 XI0).l L DgJ8 enc)) (π : FlatProof) =>
  embedMsgs dgOf (MC) (mdAppend (RM) (BM) da (dsb, dsm)) (openAllOf (merkleSkels (MC)) (flatTrees (XI170 XI0) π)) (msgsOf (XI170 XI0) π).toList

open ProximityGap CoreDefinitions NockvmE2E.Succ.Numbers NockvmE2E.Merkle.Reduction NockvmE2E.Merkle.Good SoundnessWorld SoundnessCoupling
  BadBound MerkleTreeMultiExtractability in
/-- **`exec_e2e`**: the flat (executable) verifier `verifyFlat`, run on the flat views of the ONE random oracle of the audited theorem,
accepts a false claim with probability `≤ 2^-82` against any adversary with the audited query bounds. -/
theorem exec_e2e {Statement Salt W : Type} [DecidableEq Statement] [DecidableEq Salt] [Finite Statement] [Finite Salt]
    [Finite (NQuery (merkleSkels (MC)))]
    [SampleableType (∀ dd, succinctRange DgJ8 (OPN) (NQuery (merkleSkels (MC))) Statement Salt (MC) dd)]
    (hl : XI0.l = 170)
    (encZ : Statement × Salt → List ℕ) (decZ : List ℕ → Statement × Salt) (hz : ∀ x, decZ (encZ x) = x)
    (da : MDec (RM)) (dsb : RDec (batchRound KC)) (dsm : MDec (friMask s1 d (XI170 XI0).l L DgJ8 enc))
    (vTOf : Array (Array VF.K3) → ι × Fin r → KC)
    (encB : B ↪ DgJ8) (rk : ∀ r, {c : ι ⊕ Fin P.nq // P.colRoundX c = r} ≃ Fin (Wb (XI170 XI0) r))
    (hn1 : 1 ≤ (XI170 XI0).nD) (hmd : md = mdX (XI170 XI0) hn1 P.colRoundX rk encB) (hL : L = LX (XI170 XI0) hn32) (hPS : PubSound (XI170 XI0) PR)
    (R : Resid XI0 hn32 P A R0 Rest RestV e I0 I Ifin d enc md L PR encZ decZ da dsb dsm vTOf)
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
      Q_FS (verifiedFS (trueGuards _) (embedAdv DgJ8 (EMB da dsb dsm) Aflat)))
    (hHq : IsQueryBoundP (embedAdv DgJ8 (EMB da dsb dsm) Aflat)
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
        AccF XI0 hn32 P A R0 Rest RestV e I0 I Ifin d enc md L encZ decZ (mdAppend (RM) (BM) da (dsb, dsm)) g (z, salt) π ∧ ¬ R0.Holds] ≤ (2 ^ 82 : ℝ≥0∞)⁻¹ := by
  have hdom' : 2 ^ (∑ j, ((s1) j).val) * d.val ≤ 2 ^ (XI170 XI0).nD := by
    have : 2 ^ (∑ j, ((s1) j).val) * d.val ≤ 64 * (2 ^ (∑ j, ((s1) j).val) * d.val) := by omega
    exact this.trans hrate
  have hfin := exec_e2e_of_pointwise P A R0 Rest RestV e I0 I Ifin 4 s1 d DgJ8 enc md L (idModel _) (trueGuards _) hR0 hlink hnb hRest errOld herr0
    (fun _ => rfl) hrate hn32 hF hm htoPoly hns hD hH hnq herrOld (by norm_num) hDg (EMB da dsb dsm)
    (fun g zs π => AccF XI0 hn32 P A R0 Rest RestV e I0 I Ifin d enc md L encZ decZ (mdAppend (RM) (BM) da (dsb, dsm)) g zs π)
    (fun g zs π hacc => verifyFlat_sound_tab _ hn32 P A R0 Rest RestV e I0 I Ifin d enc md L hdom' PR encZ decZ hz da dsb dsm vTOf encB rk hn1 hmd hL hPS R g zs π hacc)
    Aflat Q_FS Q_H V Pn hQFS hQH hV hFS hHq hterm hconfig
  convert hfin using 6
  rename_i o
  rcases o with _ | ⟨z, salt, π, w⟩ <;> exact Iff.rfl

end Main
#print axioms tabEval_succinctVerifyK
#print axioms roundNl_fri_ne
#print axioms rapLinks_of_uni'
#print axioms verifyFlat_sound_tab_gen
#print axioms verifyFlat_sound_tab
#print axioms exec_e2e

end NockvmE2E.Exec.E2EMain
