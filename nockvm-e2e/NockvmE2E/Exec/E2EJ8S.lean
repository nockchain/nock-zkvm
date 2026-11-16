import NockvmE2E.Exec.E2EJ8

/-!
`hRVU_X_of'` = `hRVU_X_of` (Exec/E2EJ8.lean) WITHOUT the binder `hslots`. After `limbs_surj` was
strengthened (limbs `< p`) and `k3Of` made canonical (`canon3_k3Of`), the slot canonicity is a theorem (`hslots_X`).
-/


open BinaryTree InductiveMerkleTree OracleComp OracleSpec ProtocolSpec Polynomial
open Interaction.Oracle Interaction.Oracle.Security Interaction.Oracle.Security.StateRestoration
open Interaction.Oracle.FiatShamir
open Fri.Spec Domain
open BatchedFri.Spec BatchedFri.Spec.BatchingRound
open scoped NNReal ENNReal

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace NockvmE2E.Exec.E2EJ8S
open NockvmE2E.Exec NockvmE2E.Exec.V NockvmE2E.Exec.VL NockvmE2E.Merkle NockvmE2E.Exec.E2E NockvmE2E.Exec.Emb NockvmE2E.FriPort
  NockvmE2E.Exec.E2EFri NockvmE2E.Exec.E2EMain NockvmE2E.Exec.E2EResid NockvmE2E.Exec.E2EW0 NockvmE2E.Exec.E2EFinal
  NockvmE2E.Exec.InstGen
open NockvmE2E.Succ NockvmE2E.Deep NockvmE2E.Succ.FriC NockvmE2E.FriPort NockvmE2E.FriPort.Batched
  NockvmE2E.Succ.FriDeep NockvmE2E.Succ.App NockvmE2E.Lift NockvmE2E.Lift.Alternating
  NockvmE2E.Exec.Inst NockvmE2E.Rap NockvmE2E.Merkle.RapFriQ NockvmE2E.Merkle.MA NockvmE2E.Exec.SL NockvmE2E.Exec.Cover
  NockvmE2E.Exec.SF NockvmE2E.Merkle.Fri NockvmE2E.Exec.Layout NockvmE2E.Exec.SM NockvmE2E.J8 NockvmE2E.Exec.E2ELR
open NockvmE2E.Exec.E2EJ8 NockvmE2E.Exec.E2EJ8.J8X
open NockvmE2E.J8.InstJ8 (Datum DatumOK J8 PbOfX PosX posX_of_shape hNof ω0 StmtP PubP)
open NockvmE2E.J8.TieJ8G (Inst HopsOK NumOK RdSpec Gflat hsz_of_hops gbJ hdagU_J8 hoff_J8 hdom_J8 colJ pubJ chalK)
open NockvmE2E.J8.InstJ8W (sigmaX RJ8 hfree_J8)

theorem blockEnc_lt {Φ : CoinFrame} {b n : ℕ} (sl : {i : Fin Φ.n // Φ.sampledAfter i = b} ≃ Fin n) (c : Block Φ KC b) :
    ∀ v ∈ blockEnc sl c, v < NockvmE2E.Exec.p := by
  intro v hv
  unfold blockEnc at hv
  obtain ⟨s, _, hs⟩ := List.mem_flatMap.mp hv
  exact limbs_lt_of_canon3 _ (canon3_k3Of _) v hs

variable (XI0 : ExecInst) (hn32 : (XI170 XI0).nD ≤ 32) (hsh : J8Shape.j8ShapeOk (XI170 XI0) = true)

set_option hygiene false in
local notation "ωS" => smoothDomain (XI170 XI0).nD hn32
set_option hygiene false in
local notation "s1" => (fun _ : Fin ((XI170 XI0).k + 1) => (1 : ℕ+))

variable [SampleableType KC]
variable (D : DatX (XI170 XI0) hsh) (hdk : DatumOK D.d)
/- the table restriction is kept ABSTRACT (a concrete `RJ8 …` makes `Fin (RJ8 …).ns'` vs `Fin (minusT …).ns` unification run for
minutes, TieJ8G finding); the final instance is `R := RJ8 XI d hd`, `hT := rfl`, `hσ := fun _ => rfl`, `hfree := hfree_J8 …`
(= `Inst.ofRJ8`, see `exec_e2e_J8_RJ8` at the end). -/
variable (R : TabRestr (J8 D.d hdk)) (hT : R.T' = (XI170 XI0).tabs.size)
  (hσ : ∀ t : Fin R.T', R.σ t = sigmaX (XI170 XI0) (Fin.cast hT t)) (hfree : (J8 D.d hdk).AccOn R.q)

set_option hygiene false in
local notation "IX" => (⟨XI170 XI0, hsh, posX_of_shape hsh, D.kroots, D.krootsV, D.Rt, D.regs, D.ids, D.idx, D.rk, D.lay, D.d, D.hd,
  hdk, D.hdN, D.hdω, R, hT, hσ, hfree⟩ : Inst)

variable (npub : ℕ) (tp : Fin (IX).Jm.T) (hcap : (IX).Cap npub)

set_option hygiene false in
local notation "JXn" => (IX).JJ npub tp hcap
variable (pr : PubRead JXn) (dF : ℕ+) (hNH : friBound s1 dF ≤ (JXn).H.card)
  (hpd : ∀ j c, (JXn).pre j = some c → c.natDegree ≤ (JXn).H.card)
  (ders : Array NockvmE2E.Exec.Aux.Der) (cmeta : Array (ℕ × ℕ)) (hnum : ∀ t, NumOK (IX).d (sigmaX (IX).XI t))
  (hops : HopsOK IX ders cmeta)

set_option hygiene false in
local notation "GX" => Gflat IX (hsz_of_hops IX ders cmeta hnum hops)
set_option hygiene false in
local notation "PJ" => (deepParamsJ JXn pr ωS (31 / 64) (friBound s1 dF) hNH hpd).regroup GX gbJ
set_option hygiene false in
local notation "AJ" => (airJ JXn pr ωS (31 / 64) (friBound s1 dF) hNH hpd).regroup GX gbJ
set_option hygiene false in
local notation "R0P" => R0J JXn pr ωS (31 / 64) (friBound s1 dF)
set_option hygiene false in
local notation "RestP" => RestJ JXn pr ωS (31 / 64) (friBound s1 dF) hNH hpd
set_option hygiene false in
local notation "RestVP" => RestVJ JXn pr ωS (31 / 64) (friBound s1 dF) hNH hpd

variable (cI : (JXn).ι0 ≃ Fin (XI170 XI0).nc) {m : ℕ} (hm : m + 1 = (XI170 XI0).nc * (JXn).r + (PJ).nq)

set_option hygiene false in
local notation "EJ" => eOf (XI170 XI0) cI (JXn).r hm

variable [DecidableEq ((PJ).statement (R0P) (RestP)).M0] [Finite ((PJ).statement (R0P) (RestP)).M0]
  [DecidableEq (friPlan (ω := ωS) (PJ) (AJ) (R0P) (RestP) (RestVP) (EJ)).Mfin]
  [Finite (friPlan (ω := ωS) (PJ) (AJ) (R0P) (RestP) (RestVP) (EJ)).Mfin]
  (I0 : OracleInterface ((PJ).statement (R0P) (RestP)).M0)
  (I : (r : ℕ) → OracleInterface (Cols (PJ).colRoundX (Fin (2 ^ (XI170 XI0).nD) → ZMod NockvmE2E.Exec.p) r))
  (Ifin : OracleInterface (friPlan (ω := ωS) (PJ) (AJ) (R0P) (RestP) (RestVP) (EJ)).Mfin)
variable [∀ j, SampleableType ((pSpec (XI170 XI0).k (ω := ωS) s1 (XI170 XI0).l).Challenge j)]
variable (enc : KC ↪ DgJ8)
  (md : PointMaskData (PJ).colRoundX (Fin (2 ^ (XI170 XI0).nD)) (ZMod NockvmE2E.Exec.p) DgJ8) (L : Fri.FriLeaves (ω := ωS) s1)
  {n0 n1 : ℕ} (sl0 : {i : Fin (extFrame (JXn).Φ0 2).n // (extFrame (JXn).Φ0 2).sampledAfter i = 0} ≃ Fin n0)
  (sl1 : {i : Fin (extFrame (JXn).Φ0 2).n // (extFrame (JXn).Φ0 2).sampledAfter i = 1} ≃ Fin n1)
  (m0 : ((PJ).statement (R0P) (RestP)).M0) (mf : (R0P).Mfin)

set_option hygiene false in
local notation "MC" => msC (PJ) (AJ) (R0P) (RestP) (RestVP) (EJ) I0 I Ifin 4 s1 dF (XI170 XI0).l DgJ8 enc md L (S := KC)
set_option hygiene false in
local notation "RM" => RapP.rapMask (extFrame (JXn).Φ0 2) KC md.toRapMaskData ((PJ).statement (R0P) (RestP)).M0
  (friPlan (ω := ωS) (PJ) (AJ) (R0P) (RestP) (RestVP) (EJ)).Mfin I0 I Ifin 4
set_option hygiene false in
local notation "BM" => bmask (S := KC) s1 dF (XI170 XI0).l DgJ8 enc L
set_option hygiene false in
local notation "OPN" => OpenAll DgJ8 (merkleSkels (MC))
set_option hygiene false in
local notation "DA" => daOf (XI170 XI0) hn32 (PJ) (AJ) (R0P) (RestP) (RestVP) (EJ) I0 I Ifin DgJ8 md cI sl0 sl1 (PJ).ha (PJ).hz
  (single_az (XI170 XI0) JXn pr (ω := ωS) (31 / 64) (friBound s1 dF) hNH hpd).1
  (single_az (XI170 XI0) JXn pr (ω := ωS) (31 / 64) (friBound s1 dF) hNH hpd).2 m0 mf
theorem hRVU_X_of' (hS : StmtP D.d) (hlink : NockvmE2E.J8.RVUJ8.InpLink D.d (XI170 XI0).pubIn)
    (hids : ∀ id ∈ D.d.Pb.regs, id < NockvmE2E.J8.InstJ8.P)
    (hpJ : D.d.Pb.nJ = 0 → (XI170 XI0).pubLay.present[3]! = false)
    (hpV : D.d.Pb.krootsV = 0 → (XI170 XI0).pubLay.present[5]! = false)
    (hχ : ∀ (c0 : Block (extFrame (JXn).Φ0 2) KC 0) (c1 : Block (extFrame (JXn).Φ0 2) KC 1)
      (c2 : Block (extFrame (JXn).Φ0 2) KC 2) (c3 : Block (extFrame (JXn).Φ0 2) KC 3) (i : Fin 19),
      restr 2 (chiOfBlocks c0 c1 c2 c3) i =
        toKV (SP.coinsOf (slotsAt (XI170 XI0) (blockEnc sl0 c0) (blockEnc sl1 c1)) (XI170 XI0).slotOf)[i.val]!)
    (hrd : ∀ (c0 : Block (extFrame (JXn).Φ0 2) KC 0) (c1 : Block (extFrame (JXn).Φ0 2) KC 1)
      (c2 : Block (extFrame (JXn).Φ0 2) KC 2) (c3 : Block (extFrame (JXn).Φ0 2) KC 3) (vT : Array (Array VF.K3)) (vQ : Array VF.K3),
      VShape (XI170 XI0) vT vQ →
      PubJ8P (XI170 XI0).pubIn (XI170 XI0).pubLay (XI170 XI0).slotOf
        (slotsAt (XI170 XI0) (blockEnc sl0 c0) (blockEnc sl1 c1)) (pubAt (XI170 XI0) vT) →
      ∃ pub : Array UInt64, (∀ g ∈ pub, canon g) ∧
        PubJ8P (XI170 XI0).pubIn (XI170 XI0).pubLay (XI170 XI0).slotOf
          (slotsAt (XI170 XI0) (blockEnc sl0 c0) (blockEnc sl1 c1)) pub ∧
        pr.rd (fun c => (finDecG (XI170 XI0) cI (JXn).r (PJ).nq mf (deepMsg vT vQ)).2.1 (c, 0)) =
          NockvmE2E.J8.RVUJ8.Mof (XI170 XI0).pubLay pub) :
    ∀ (c0 : Block (extFrame (JXn).Φ0 2) KC 0) (c1 : Block (extFrame (JXn).Φ0 2) KC 1)
      (c2 : Block (extFrame (JXn).Φ0 2) KC 2) (c3 : Block (extFrame (JXn).Φ0 2) KC 3) (vT : Array (Array VF.K3)) (vQ : Array VF.K3),
      VShape (XI170 XI0) vT vQ →
      PubJ8P (XI170 XI0).pubIn (XI170 XI0).pubLay (XI170 XI0).slotOf
        (slotsAt (XI170 XI0) (blockEnc sl0 c0) (blockEnc sl1 c1)) (pubAt (XI170 XI0) vT) →
      (RestVP) m0 (finDecG (XI170 XI0) cI (JXn).r (PJ).nq mf (deepMsg vT vQ)) (chiOfBlocks c0 c1 c2 c3) := by
  intro c0 c1 c2 c3 vT vQ hV hP
  have hslots_X : ∀ (c0 : Block (extFrame (JXn).Φ0 2) KC 0) (c1 : Block (extFrame (JXn).Φ0 2) KC 1),
      ∀ s ∈ slotsAt (XI170 XI0) (blockEnc sl0 c0) (blockEnc sl1 c1), canon3 s := by
    intro c0 c1 s hs
    unfold slotsAt at hs
    refine canon_slots _ _ ?_ s hs
    intro x hx
    rcases Array.mem_append.mp hx with hx | hx
    · exact canon_k3s _ (blockEnc_lt sl0 c0) _ x hx
    · exact canon_k3s _ (blockEnc_lt sl1 c1) _ x hx
  obtain ⟨pub, hcan, hP', hrd'⟩ := hrd c0 c1 c2 c3 vT vQ hV hP
  refine ⟨?_, hS⟩
  show PubP D.d (restr 2 (chiOfBlocks c0 c1 c2 c3))
    (pr.rd (fun c => (finDecG (XI170 XI0) cI (JXn).r (PJ).nq mf (deepMsg vT vQ)).2.1 (c, 0)))
  rw [hrd']
  exact NockvmE2E.J8.RVUJ8.hRVU_J8 D.d hS _ hlink _ _ _ pub (hslots_X c0 c1) hcan hids hpJ hpV _ (hχ c0 c1 c2 c3) hP'

end NockvmE2E.Exec.E2EJ8S

#print axioms NockvmE2E.Exec.E2EJ8S.hRVU_X_of'
