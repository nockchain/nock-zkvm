/-
the J-9 A twin of `J8/RVUJ8.lean`.
 * §1 `PubJ9Rel` (the eight conjuncts of nock `PubEq9A`, InstJ9A.lean:310), `checkPubEq9_sound`, `pubCheck9_sound`
   (twins of `SP.PubJ8Rel`, `SP.checkPubEq_sound`, `SP.pubCheck_sound`): the verifier-side eight-table check gives the relation.
 * §2 `hRVU_J9A`: that relation (`PubJ9P`) gives nock's `PubP9A d χ (Mof9 L pub)`.
-/
import NockvmE2E.J9A.InstJ9A
import NockvmE2E.J8.RVUJ8
import NockvmE2E.Exec.PubExe9

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace NockvmE2E.J9A.RVUJ9A

open NockvmE2E.Exec NockvmE2E.Exec.SP NockvmE2E.Exec.VL

/-! ## 1. The relation and the soundness of the executable check -/

/-- the eight conjuncts of `PubEq9A` over the verifier's data (cf. `SP.PubJ8Rel`): conjunct 1 gains the axis path `pubAXp = 2`,
conjunct 2 the axis service `pubAXs = 0` (left) and the split terminal `pubSPs = 0` (right) -/
noncomputable def PubJ9Rel (χ : Fin 19 → KC) (ρ : Fin 5 → Q) (ρS : Q)
    (pubsC pubsW pubsJ pubsA pubsV pubsX pubsS : ℕ → KC)
    (pinConsR : List (Fin 8 → Q)) (claimRecs pinRecs : List (Fin 5 → Q)) : Prop :=
  (ρ 3 + (qmk (pubsW 4) (pubsW (4 + 1)) + qmk (pubsJ 2) (pubsJ 3)) = qmk (pubsC 4) (pubsC (4 + 1))) ∧
  (ρ 4 + qmk (pubsX 2) (pubsX (2 + 1)) = qmk (pubsW 6) (pubsW (6 + 1))) ∧
  (ρS + (pinConsR.map fun r => qinv (compressQ (qmk (χ 11) (χ 15)) (qmk (χ 12) (χ 16)) r)).sum
      + qmk (pubsJ 0) (pubsJ 1) + qmk (pubsX 0) (pubsX (0 + 1)) =
    qmk (pubsA 8) (pubsA (8 + 1)) + qmk (pubsV 6) (pubsV (6 + 1)) + qmk (pubsS 0) (pubsS (0 + 1))) ∧
  (((claimRecs ++ pinRecs).map fun r => qinv (compressQ (m := 5) (qmk (χ 4) (χ 6)) (qmk (χ 5) (χ 7)) r)).sum =
    qmk (pubsC 0) (pubsC 1) + qmk (pubsA 6) (pubsA (6 + 1))) ∧
  (qmk (pubsA 4) (pubsA (4 + 1)) = qmk (pubsA 10) (pubsA (10 + 1)) + qmk (pubsV 4) (pubsV (4 + 1))) ∧
  (pubsA 0 = 0 ∧ pubsA 1 = 0) ∧
  (pubsC 2 = pubsW 0 ∧ pubsC 3 = pubsW 1) ∧
  (pubsA 2 = pubsV 0 ∧ pubsA 3 = pubsV 1)

section Main
open PE

theorem checkPubEq9_sound (inp : PubIn) (coins : Array VF.K3) (ps : PubSet9)
    (hc : ∀ i : ℕ, canon3 coins[i]!)
    (h0 : ArrCan ps.compute) (h1 : ArrCan ps.cell) (h2 : ArrCan ps.walkJ8) (h3 : ArrCan ps.jet)
    (h4 : ArrCan ps.atom) (h5 : ArrCan ps.walkAtom) (h6 : ArrCan ps.axis) (h7 : ArrCan ps.split) (hinp : InpCan inp)
    (h : checkPubEq9 inp coins ps = true) :
    (∃ cr pr : List (List K6),
      inp.claimCells.mapM (claimRecS ⟨coins[2]!, coins[3]!⟩ ⟨coins[17]!, coins[18]!⟩ ps.compute) = some cr ∧
      inp.pins.mapM (pinRecS ⟨coins[2]!, coins[3]!⟩ ⟨coins[17]!, coins[18]!⟩) = some pr ∧
      PubJ9Rel (fun i : Fin 19 => toKV coins[(i : ℕ)]!) (rhoOf ps.compute) (rhoSOf ps.compute) (pubK ps.cell)
        (pubK ps.walkJ8) (pubK ps.jet) (pubK ps.atom) (pubK ps.walkAtom) (pubK ps.axis) (pubK ps.split)
        (inp.pins.map fun q => (recQ (PE.pinConsKey q.key q.idx) : Fin 8 → Q))
        (cr.map fun r => (recQ r : Fin 5 → Q)) (pr.map fun r => (recQ r : Fin 5 → Q))) ∧
      ComputeDerivedP inp coins ps.compute := by
  unfold checkPubEq9 at h
  simp only [] at h
  split at h
  · simp at h
  have h := getD_true h
  obtain ⟨cr, hcr, h⟩ := bind_some h
  obtain ⟨pr, hpr, h⟩ := bind_some h
  obtain ⟨w0, hw0, h⟩ := bind_some h
  obtain ⟨j2, hj2, h⟩ := bind_some h
  obtain ⟨ch, hch, h⟩ := bind_some h
  obtain ⟨w1, hw1, h⟩ := bind_some h
  obtain ⟨axp, haxp, h⟩ := bind_some h
  obtain ⟨axs, haxs, h⟩ := bind_some h
  obtain ⟨sps, hsps, h⟩ := bind_some h
  obtain ⟨j0, hj0, h⟩ := bind_some h
  obtain ⟨aMI, haMI, h⟩ := bind_some h
  obtain ⟨v1, hv1, h⟩ := bind_some h
  obtain ⟨c0, hc0, h⟩ := bind_some h
  obtain ⟨aMB, haMB, h⟩ := bind_some h
  obtain ⟨aHQ, haHQ, h⟩ := bind_some h
  obtain ⟨aC, haC, h⟩ := bind_some h
  obtain ⟨v0, hv0, h⟩ := bind_some h
  obtain ⟨a0, ha0, h⟩ := bind_some h
  obtain ⟨a1, ha1, h⟩ := bind_some h
  obtain ⟨a2, ha2, h⟩ := bind_some h
  obtain ⟨a3, ha3, h⟩ := bind_some h
  obtain ⟨c2, hc2, h⟩ := bind_some h
  obtain ⟨c3, hc3, h⟩ := bind_some h
  obtain ⟨wk0, hwk0, h⟩ := bind_some h
  obtain ⟨wk1, hwk1, h⟩ := bind_some h
  obtain ⟨va0, hva0, h⟩ := bind_some h
  obtain ⟨va1, hva1, h⟩ := bind_some h
  have hfin := Option.some.inj h
  clear h
  simp only [Bool.and_eq_true] at hfin
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨e0, e1⟩, e2⟩, e3⟩, e4⟩, e5⟩, e6a, e6b⟩, e7a, e7b⟩, e8a, e8b⟩ := hfin
  have hz : canon6 ⟨coins[2]!, coins[3]!⟩ := ⟨hc 2, hc 3⟩
  have hy : canon6 ⟨coins[17]!, coins[18]!⟩ := ⟨hc 17, hc 18⟩
  have hgh : canon6 ⟨coins[11]!, coins[15]!⟩ := ⟨hc 11, hc 15⟩
  have hrh : canon6 ⟨coins[12]!, coins[16]!⟩ := ⟨hc 12, hc 16⟩
  have hgv : canon6 ⟨coins[4]!, coins[6]!⟩ := ⟨hc 4, hc 6⟩
  have hrv : canon6 ⟨coins[5]!, coins[7]!⟩ := ⟨hc 5, hc 7⟩
  have hcr' : inp.claimCells.mapM (claimRecS ⟨coins[2]!, coins[3]!⟩ ⟨coins[17]!, coins[18]!⟩ ps.compute) = some cr := hcr
  have hpr' : inp.pins.mapM (pinRecS ⟨coins[2]!, coins[3]!⟩ ⟨coins[17]!, coins[18]!⟩) = some pr := hpr
  have hcrc : ∀ r ∈ cr, r.length = 5 ∧ ∀ w ∈ r, canon6 w := by
    intro r hr
    obtain ⟨c, hcm, hcc⟩ := mapM_mem _ _ _ hcr' r hr
    have := hinp.1 c hcm
    exact claimRecS_can _ _ _ hz hy h0 c this.1 this.2 r hcc
  have hprc : ∀ r ∈ pr, r.length = 5 ∧ ∀ w ∈ r, canon6 w := by
    intro r hr
    obtain ⟨q, hqm, hqc⟩ := mapM_mem _ _ _ hpr' r hr
    have := hinp.2 q hqm
    exact pinRecS_can _ _ hz hy q this.2.1 this.2.2.1 this.2.2.2 r hqc
  refine ⟨⟨cr, pr, hcr', hpr', ?_⟩, computeDerivedOk_sound inp coins ps.compute hc h0 e0⟩
  have cr3 : canon6 (K6.mk (VF.K3.mk ps.compute[15]! ps.compute[15 + 1]! ps.compute[15 + 2]!)
      (VF.K3.mk ps.compute[21]! ps.compute[21 + 1]! ps.compute[21 + 2]!)) :=
    ⟨⟨h0 _, h0 _, h0 _⟩, ⟨h0 _, h0 _, h0 _⟩⟩
  have cr4 : canon6 (K6.mk (VF.K3.mk ps.compute[18]! ps.compute[18 + 1]! ps.compute[18 + 2]!)
      (VF.K3.mk ps.compute[24]! ps.compute[24 + 1]! ps.compute[24 + 2]!)) :=
    ⟨⟨h0 _, h0 _, h0 _⟩, ⟨h0 _, h0 _, h0 _⟩⟩
  have crS : canon6 (K6.mk (VF.K3.mk ps.compute[27]! ps.compute[27 + 1]! ps.compute[27 + 2]!)
      (VF.K3.mk ps.compute[30]! ps.compute[30 + 1]! ps.compute[30 + 2]!)) :=
    ⟨⟨h0 _, h0 _, h0 _⟩, ⟨h0 _, h0 _, h0 _⟩⟩
  have t3 : rhoOf ps.compute 3 = toQ6 (K6.mk (VF.K3.mk ps.compute[15]! ps.compute[15 + 1]! ps.compute[15 + 2]!)
      (VF.K3.mk ps.compute[21]! ps.compute[21 + 1]! ps.compute[21 + 2]!)) := by simp [rhoOf]; rfl
  have t4 : rhoOf ps.compute 4 = toQ6 (K6.mk (VF.K3.mk ps.compute[18]! ps.compute[18 + 1]! ps.compute[18 + 2]!)
      (VF.K3.mk ps.compute[24]! ps.compute[24 + 1]! ps.compute[24 + 2]!)) := by simp [rhoOf]; rfl
  have tS : rhoSOf ps.compute = toQ6 (K6.mk (VF.K3.mk ps.compute[27]! ps.compute[27 + 1]! ps.compute[27 + 2]!)
      (VF.K3.mk ps.compute[30]! ps.compute[30 + 1]! ps.compute[30 + 2]!)) := rfl
  obtain ⟨cw0, tw0⟩ := pp_some _ h2 _ _ hw0
  obtain ⟨cj2, tj2⟩ := pp_some _ h3 _ _ hj2
  obtain ⟨cch, tch⟩ := pp_some _ h1 _ _ hch
  obtain ⟨cw1, tw1⟩ := pp_some _ h2 _ _ hw1
  obtain ⟨caxp, taxp⟩ := pp_some _ h6 _ _ haxp
  obtain ⟨caxs, taxs⟩ := pp_some _ h6 _ _ haxs
  obtain ⟨csps, tsps⟩ := pp_some _ h7 _ _ hsps
  obtain ⟨cj0, tj0⟩ := pp_some _ h3 _ _ hj0
  obtain ⟨caMI, taMI⟩ := pp_some _ h4 _ _ haMI
  obtain ⟨cv1, tv1⟩ := pp_some _ h5 _ _ hv1
  obtain ⟨cc0, tc0⟩ := pp_some _ h1 _ _ hc0
  obtain ⟨caMB, taMB⟩ := pp_some _ h4 _ _ haMB
  obtain ⟨caHQ, taHQ⟩ := pp_some _ h4 _ _ haHQ
  obtain ⟨caC, taC⟩ := pp_some _ h4 _ _ haC
  obtain ⟨cv0, tv0⟩ := pp_some _ h5 _ _ hv0
  have hpin := foldl_invSum (fun q : NounRec => PE.compress ⟨coins[11]!, coins[15]!⟩ ⟨coins[12]!, coins[16]!⟩
    (PE.pinConsKey q.key q.idx)) inp.pins K6.zero canon6_zero
  have hpinq : (inp.pins.map fun q => qinv (toQ6 (PE.compress ⟨coins[11]!, coins[15]!⟩ ⟨coins[12]!, coins[16]!⟩
      (PE.pinConsKey q.key q.idx)))).sum =
      ((inp.pins.map fun q => (recQ (PE.pinConsKey q.key q.idx) : Fin 8 → Q)).map fun r =>
        qinv (compressQ (qmk (toKV coins[11]!) (toKV coins[15]!)) (qmk (toKV coins[12]!) (toKV coins[16]!)) r)).sum := by
    rw [List.map_map]
    refine congrArg List.sum (List.map_congr_left fun q hq => ?_)
    have hk := hinp.2 q hq
    have hkc := pinConsKey_can q.key q.idx hk.1 hk.2.1
    simp only [Function.comp]
    rw [(toQ6_compress _ _ _ hkc.1 hgh hrh hkc.2).2]
    rfl
  have hpinc : canon6 (inp.pins.foldl (fun s q => PE.K6.add s (PE.compress ⟨coins[11]!, coins[15]!⟩ ⟨coins[12]!, coins[16]!⟩
    (PE.pinConsKey q.key q.idx)).inv0) K6.zero) := hpin.1
  have hcl := foldl_invSum (fun r : List K6 => PE.compress ⟨coins[4]!, coins[6]!⟩ ⟨coins[5]!, coins[7]!⟩ r)
    (cr ++ pr) K6.zero canon6_zero
  have hclq : ((cr ++ pr).map fun r => qinv (toQ6 (PE.compress ⟨coins[4]!, coins[6]!⟩ ⟨coins[5]!, coins[7]!⟩ r))).sum =
      (((cr.map fun r => (recQ r : Fin 5 → Q)) ++ (pr.map fun r => (recQ r : Fin 5 → Q))).map fun r =>
        qinv (compressQ (m := 5) (qmk (toKV coins[4]!) (toKV coins[6]!)) (qmk (toKV coins[5]!) (toKV coins[7]!)) r)).sum := by
    rw [← List.map_append, List.map_map]
    refine congrArg List.sum (List.map_congr_left fun r hr => ?_)
    have hrc : r.length = 5 ∧ ∀ w ∈ r, canon6 w := by
      rcases List.mem_append.mp hr with hr | hr
      · exact hcrc r hr
      · exact hprc r hr
    simp only [Function.comp]
    rw [(toQ6_compress _ _ _ hrc.1 hgv hrv hrc.2).2]
    rfl
  obtain ⟨ca0, ta0⟩ := kv_some _ h4 _ _ ha0
  obtain ⟨ca1, ta1⟩ := kv_some _ h4 _ _ ha1
  obtain ⟨ca2, ta2⟩ := kv_some _ h4 _ _ ha2
  obtain ⟨ca3, ta3⟩ := kv_some _ h4 _ _ ha3
  obtain ⟨cc2, tc2⟩ := kv_some _ h1 _ _ hc2
  obtain ⟨cc3, tc3⟩ := kv_some _ h1 _ _ hc3
  obtain ⟨cwk0, twk0⟩ := kv_some _ h2 _ _ hwk0
  obtain ⟨cwk1, twk1⟩ := kv_some _ h2 _ _ hwk1
  obtain ⟨cva0, tva0⟩ := kv_some _ h5 _ _ hva0
  obtain ⟨cva1, tva1⟩ := kv_some _ h5 _ _ hva1
  refine ⟨?_, ?_, ?_, ?_, ?_, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · have E := congrArg toQ6 (beq_K6 e1)
    rw [toQ6_add _ _ cr3 (canon6_add _ _ cw0 cj2), toQ6_add _ _ cw0 cj2, tw0, tj2, tch] at E
    rw [t3]; exact E
  · have E := congrArg toQ6 (beq_K6 e2)
    rw [toQ6_add _ _ cr4 caxp, taxp, tw1] at E
    rw [t4]; exact E
  · have E := congrArg toQ6 (beq_K6 e3)
    rw [toQ6_add _ _ (canon6_add _ _ (canon6_add _ _ crS hpinc) cj0) caxs, toQ6_add _ _ (canon6_add _ _ crS hpinc) cj0,
      toQ6_add _ _ crS hpinc, toQ6_add _ _ (canon6_add _ _ caMI cv1) csps, toQ6_add _ _ caMI cv1, taMI, tv1, tj0, taxs, tsps,
      hpin.2, hpinq, toQ6_zero, zero_add] at E
    rw [tS]; exact E
  · have E := congrArg toQ6 (beq_K6 e4)
    rw [toQ6_add _ _ cc0 caMB, tc0, taMB, hcl.2, hclq, toQ6_zero, zero_add] at E
    exact E
  · have E := congrArg toQ6 (beq_K6 e5)
    rw [toQ6_add _ _ caC cv0, taHQ, taC, tv0] at E
    exact E
  · rw [← ta0]; exact isZero_toKV _ e6a
  · rw [← ta1]; exact isZero_toKV _ e6b
  · rw [← tc2, ← twk0, beq_K3 e7a]
  · rw [← tc3, ← twk1, beq_K3 e7b]
  · rw [← ta2, ← tva0, beq_K3 e8a]
  · rw [← ta3, ← tva1, beq_K3 e8b]
end Main

/-- the verifier-side public relation of the J-9 A objects (twin of `PubJ8P`) -/
def PubJ9P (inp : PE.PubIn) (L : PE.PubLayout) (slotOf : Array Nat) (slots : Array VF.K3) (pub : Array UInt64) : Prop :=
  (∃ cr pr : List (List PE.K6),
      inp.claimCells.mapM (claimRecS ⟨(coinsOf slots slotOf)[2]!, (coinsOf slots slotOf)[3]!⟩
        ⟨(coinsOf slots slotOf)[17]!, (coinsOf slots slotOf)[18]!⟩ (slOf L pub 0)) = some cr ∧
      inp.pins.mapM (pinRecS ⟨(coinsOf slots slotOf)[2]!, (coinsOf slots slotOf)[3]!⟩
        ⟨(coinsOf slots slotOf)[17]!, (coinsOf slots slotOf)[18]!⟩) = some pr ∧
      PubJ9Rel (fun i : Fin 19 => toKV (coinsOf slots slotOf)[(i : ℕ)]!) (rhoOf (slOf L pub 0))
        (rhoSOf (slOf L pub 0)) (pubK (slOf L pub 1)) (pubK (slOf L pub 2)) (pubK (slOf L pub 3))
        (pubK (slOf L pub 4)) (pubK (slOf L pub 5)) (pubK (slOf L pub 6)) (pubK (slOf L pub 7))
        (inp.pins.map fun q => (recQ (PE.pinConsKey q.key q.idx) : Fin 8 → Q))
        (cr.map fun r => (recQ r : Fin 5 → Q)) (pr.map fun r => (recQ r : Fin 5 → Q))) ∧
  ComputeDerivedP inp (coinsOf slots slotOf) (slOf L pub 0)

/-- **`pubCheck9_sound`**: a true eight-table check gives `PubJ9P` (canonical slots / publics / instance data) -/
theorem pubCheck9_sound (inp : PE.PubIn) (L : PE.PubLayout) (slotOf : Array Nat) (slots : Array VF.K3)
    (pub : Array UInt64) (hs : ∀ s ∈ slots, canon3 s) (hp : ∀ g ∈ pub, canon g) (hinp : InpCan inp)
    (h : PE.pubCheck9 inp L slotOf slots pub = true) : PubJ9P inp L slotOf slots pub := by
  have h1 := (PE.pubCheckG_sound 8 PE.tabLens9 PE.chk8 (fun inp co ps => PE.chk8 inp co ps = true) (fun _ _ _ h => h)
    inp L slotOf slots pub h).2
  have e : ((List.range 8).toArray.map (PE.sliceG L pub)) =
      #[slOf L pub 0, slOf L pub 1, slOf L pub 2, slOf L pub 3, slOf L pub 4, slOf L pub 5, slOf L pub 6, slOf L pub 7] := by
    simp [List.range_succ]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  rw [e] at h1
  have hc : ∀ i : ℕ, canon3 (coinsOf slots slotOf)[i]! := by
    refine canon_getBang canon3 canon3_default _ ?_
    intro g hg
    unfold coinsOf at hg
    rw [Array.mem_map] at hg
    obtain ⟨i, _, rfl⟩ := hg
    exact canon_getBang canon3 canon3_default slots hs _
  exact checkPubEq9_sound inp (coinsOf slots slotOf)
    ⟨slOf L pub 0, slOf L pub 1, slOf L pub 2, slOf L pub 3, slOf L pub 4, slOf L pub 5, slOf L pub 6, slOf L pub 7⟩ hc
    (slOf_can L pub hp 0) (slOf_can L pub hp 1) (slOf_can L pub hp 2) (slOf_can L pub hp 3) (slOf_can L pub hp 4)
    (slOf_can L pub hp 5) (slOf_can L pub hp 6) (slOf_can L pub hp 7) hinp h1


/-! ## 2. `hRVU_J9A` -/

open Polynomial
open NockvmE2E.Exec.VL
open NockvmE2E.J8.RVUJ8
open Nock.NockVMROM.Thm54.T0Tower (Quad)
open Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.ClaimJ9 (claimBigs claimBigRecs claimRecsJ9 pubVJ9 labelJ9 seedJ9 claimHJ9 claimKH isBigN)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8P (rkC claimCells)
open Nock.NockVMROM.Thm54.VclL.Handle.FrameVS (claimNoun isCellN)
open NockvmE2E.J9A.InstJ9A (Datum9A StmtP9A PubP9A Msg9)
open NockvmE2E.J8.InstJ8 (P Φ0)
open Nock.TraceGenExe (deltaF)

attribute [local instance] Nock.NockVMROM.Thm54.VclL.Handle.E2EJ8Iface.twinFact Nock.NockVMROM.Thm54.VclL.Handle.E2EJ8Iface.twinAlg

/-- **the J-9 A message read off the verifier's publics** -/
noncomputable def Mof9 (L : PE.PubLayout) (pub : Array UInt64) : Msg9 :=
  (⟨⟨fun k => ((SP.slOf L pub 0)[2 * k.val + 1]!.toNat, 0, 0),
    fun i => φ (SP.rhoOf (SP.slOf L pub 0) i), φ (SP.rhoSOf (SP.slOf L pub 0)),
    SP.pubK (SP.slOf L pub 1), SP.pubK (SP.slOf L pub 2), SP.pubK (SP.slOf L pub 3),
    SP.pubK (SP.slOf L pub 4), SP.pubK (SP.slOf L pub 5)⟩, SP.pubK (SP.slOf L pub 6), SP.pubK (SP.slOf L pub 7)⟩,
   fun j => (zv (SP.slOf L pub 0)[j.val]! : ZMod P))

/-- the claim position `k` as an executable record (a cell or a big atom; the serial is read from the labels) -/
def claimRec9 (nn : Fin 3 → Nock.Noun) (k : Fin 3) : PE.NounRec := claimRec nn k

/-- **the datum link at J-9**: the verifier's claim records are the cell nouns then the big-atom nouns of the claim, its pins the
registry templates, its atoms the SMALL atom nouns of the claim -/
structure InpLink9 (d : Datum9A) (inp : PE.PubIn) : Prop where
  hcl : inp.claimCells = (claimCells d.c).map (claimRec (claimNoun d.c)) ++ (claimBigs P d.c).map (claimRec (claimNoun d.c))
  hpin : inp.pins = d.Pb.regs.map (fun id => (⟨id, toks (Nock.Jet.Autogen.compile P (d.Pb.Rt id)), d.Pb.idx id,
    (d.Pb.rk id).1, (d.Pb.rk id).2⟩ : PE.NounRec))
  hat : inp.atoms = (List.finRange 3).filterMap (fun k => match claimNoun d.c k with
    | .atom v => if P ≤ v then none else some (k.val, v) | .cell _ _ => none)

theorem mapM_append_some {α β : Type} (f : α → Option β) : ∀ (a b : List α) (r : List β), (a ++ b).mapM f = some r →
    ∃ ra rb, a.mapM f = some ra ∧ b.mapM f = some rb ∧ r = ra ++ rb
  | [], b, r, h => ⟨[], r, by simp, by simpa using h, by simp⟩
  | x :: a, b, r, h => by
      rw [List.cons_append] at h
      obtain ⟨y, rs, hy, hrs, rfl⟩ := mapM_cons_some _ _ _ _ h
      obtain ⟨ra, rb, h1, h2, rfl⟩ := mapM_append_some f a b rs hrs
      refine ⟨y :: ra, rb, ?_, h2, rfl⟩
      rw [List.mapM_cons, hy]
      simp [h1]

theorem isBigN_atom (v : ℕ) : isBigN P (.atom v) = true ↔ P ≤ v := by simp [isBigN]

theorem claimRecS_big (z y : PE.K6) (x : Array UInt64) (k : Fin 3) (n : ℕ) (hn : P ≤ n) (hi lo : ℕ) (r : List PE.K6)
    (h : SP.claimRecS z y x ⟨k.val, toks (.atom n), 0, hi, lo⟩ = some r) :
    SP.labelOf x (2 * k.val) = 2 ∧ r = PE.claimVec (fpOf z z.inv0 y (.atom n)) (SP.labelOf x (2 * k.val + 1)) 0 0 := by
  unfold SP.claimRecS at h
  simp only [toks] at h
  have hk : ¬ (k.val > 2) := by omega
  have hb : decide (n ≥ VF.PN) = true := by simp; have : VF.PN = P := PN_eq ▸ rfl; omega
  by_cases hl : SP.labelOf x (2 * k.val) = 2
  · refine ⟨hl, ?_⟩
    have he := enc_toks z y (.atom n)
    simp only [toks] at he
    simp only [hb, hk, hl, if_true, decide_false, Bool.false_or, bne_self_eq_false, Bool.false_eq_true, ite_false] at h
    rw [he] at h
    simp only [bind, Option.bind, pure, Option.some.injEq] at h
    exact h.symm
  · exfalso
    simp [hk, hl, hb] at h

theorem claims_mapM_big (z y : PE.K6) (x : Array UInt64) (nn : Fin 3 → Nock.Noun) :
    ∀ (ks : List (Fin 3)), (∀ k ∈ ks, isBigN P (nn k) = true) → ∀ r : List (List PE.K6),
      (ks.map (claimRec nn)).mapM (SP.claimRecS z y x) = some r →
      (∀ k ∈ ks, SP.labelOf x (2 * k.val) = 2) ∧
        r = ks.map (fun k => PE.claimVec (fpOf z z.inv0 y (nn k)) (SP.labelOf x (2 * k.val + 1)) 0 0)
  | [], _, r, h => by
      simp only [List.map_nil, List.mapM_nil, pure, Option.some.injEq] at h
      subst h; simp
  | k :: ks, hk, r, h => by
      rw [List.map_cons] at h
      obtain ⟨b, rs, hb, hrs, rfl⟩ := mapM_cons_some _ _ _ _ h
      have hbig := hk k (by simp)
      have h1 : SP.labelOf x (2 * k.val) = 2 ∧ b = PE.claimVec (fpOf z z.inv0 y (nn k)) (SP.labelOf x (2 * k.val + 1)) 0 0 := by
        unfold claimRec at hb
        cases hn : nn k with
        | atom v =>
            rw [hn] at hbig
            have := (isBigN_atom v).1 hbig
            have hb' : SP.claimRecS z y x ⟨k.val, toks (.atom v), 0, (rkC (.atom v)).1, (rkC (.atom v)).2⟩ = some b := by
              rw [hn] at hb; exact hb
            have := claimRecS_big z y x k v this _ _ b hb'
            exact this
        | cell a b' => rw [hn] at hbig; simp [isBigN] at hbig
      have h2 := claims_mapM_big z y x nn ks (fun k' hk' => hk k' (by simp [hk'])) rs hrs
      refine ⟨fun k' hk' => ?_, ?_⟩
      · rcases List.mem_cons.1 hk' with rfl | hk'
        · exact h1.1
        · exact h2.1 k' hk'
      · rw [List.map_cons, h1.2, h2.2]


/-! ### labels, the seed -/

theorem hk_facts9 (d : Datum9A) (x : Array UInt64)
    (hat : ∀ k : Fin 3, ∀ v, claimNoun d.c k = .atom v → v < P → x[2 * k.val]! = 0 ∧ x[2 * k.val + 1]! = UInt64.ofNat v)
    (hcl : ∀ k : Fin 3, isCellN (claimNoun d.c k) = true → SP.labelOf x (2 * k.val) = 1)
    (hbg : ∀ k : Fin 3, isBigN P (claimNoun d.c k) = true → SP.labelOf x (2 * k.val) = 2) (k : Fin 3) :
    zP x[2 * k.val]! = (((claimHJ9 P d.c (mOf x) k).1 : ℕ) : ZMod P) ∧
      zP x[2 * k.val + 1]! = (((claimHJ9 P d.c (mOf x) k).2 : ℕ) : ZMod P) := by
  unfold claimHJ9
  rcases hn : claimNoun d.c k with v | ⟨a, b⟩
  · by_cases hv : P ≤ v
    · have h2 := hbg k (by rw [hn]; exact (isBigN_atom v).2 hv)
      simp only [claimKH, hv, ite_true]
      refine ⟨?_, rfl⟩
      unfold SP.labelOf at h2
      show ((x[2 * k.val]!).toNat : ZMod P) = _
      rw [h2]
    · have hv' : v < P := by omega
      obtain ⟨h0, h1⟩ := hat k v hn hv'
      simp only [claimKH, hv, ite_false]
      refine ⟨?_, ?_⟩
      · rw [h0]; rfl
      · rw [h1]; exact zv_ofNat _ (lt_trans hv' P_lt)
  · have hc : isCellN (claimNoun d.c k) = true := by rw [hn]; rfl
    have h1 := hcl k hc
    simp only [claimKH]
    refine ⟨?_, rfl⟩
    unfold SP.labelOf at h1
    show ((x[2 * k.val]!).toNat : ZMod P) = _
    rw [h1]

theorem labelJ9_get (d : Datum9A) (x : Array UInt64)
    (hat : ∀ k : Fin 3, ∀ v, claimNoun d.c k = .atom v → v < P → x[2 * k.val]! = 0 ∧ x[2 * k.val + 1]! = UInt64.ofNat v)
    (hcl : ∀ k : Fin 3, isCellN (claimNoun d.c k) = true → SP.labelOf x (2 * k.val) = 1)
    (hbg : ∀ k : Fin 3, isBigN P (claimNoun d.c k) = true → SP.labelOf x (2 * k.val) = 2) :
    ∀ j < 6, (labelJ9 P d.c (mOf x)).getD j 0 = zP x[j]! := by
  have h0 := hk_facts9 d x hat hcl hbg 0
  have h1 := hk_facts9 d x hat hcl hbg 1
  have h2 := hk_facts9 d x hat hcl hbg 2
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two, mul_zero, zero_add, mul_one, Nat.reduceMul, Nat.reduceAdd] at h0 h1 h2
  intro j hj
  unfold labelJ9
  interval_cases j
  · exact h0.1.symm
  · exact h0.2.symm
  · exact h1.1.symm
  · exact h1.2.symm
  · exact h2.1.symm
  · exact h2.2.symm

theorem labelJ9_list (d : Datum9A) (x : Array UInt64)
    (hat : ∀ k : Fin 3, ∀ v, claimNoun d.c k = .atom v → v < P → x[2 * k.val]! = 0 ∧ x[2 * k.val + 1]! = UInt64.ofNat v)
    (hcl : ∀ k : Fin 3, isCellN (claimNoun d.c k) = true → SP.labelOf x (2 * k.val) = 1)
    (hbg : ∀ k : Fin 3, isBigN P (claimNoun d.c k) = true → SP.labelOf x (2 * k.val) = 2) :
    labelJ9 P d.c (mOf x) = List.ofFn (fun q : Fin 6 => zP x[q.val]!) := by
  apply List.ext_getElem
  · simp [labelJ9]
  · intro n h1 h2
    have hn : n < 6 := by simpa [labelJ9] using h1
    have := labelJ9_get d x hat hcl hbg n hn
    rw [List.getD_eq_getElem _ _ h1] at this
    rw [this, List.getElem_ofFn]

theorem seed_eq9 (d : Datum9A) (x : Array UInt64)
    (hat : ∀ k : Fin 3, ∀ v, claimNoun d.c k = .atom v → v < P → x[2 * k.val]! = 0 ∧ x[2 * k.val + 1]! = UInt64.ofNat v)
    (hcl : ∀ k : Fin 3, isCellN (claimNoun d.c k) = true → SP.labelOf x (2 * k.val) = 1)
    (hbg : ∀ k : Fin 3, isBigN P (claimNoun d.c k) = true → SP.labelOf x (2 * k.val) = 2)
    (c13 c14 : KN) :
    c13 * (((labelJ9 P d.c (mOf x)).zipIdx.map fun p => c14 ^ p.2 * algebraMap (ZMod P) KN p.1).sum) =
      c13 * ∑ q : Fin 6, c14 ^ (q : ℕ) * algebraMap (ZMod P) KN (zP x[q.val]!) := by
  rw [labelJ9_list d x hat hcl hbg]
  congr 1

/-- the coin-derived compute publics `x` against `pubVJ9` -/
theorem derived9_of (d : Datum9A) (inp : PE.PubIn) (x : Array UInt64) (hx : SP.ArrCan x)
    (coins : Array VF.K3) (hder : SP.ComputeDerivedP inp coins x)
    (hat : ∀ k : Fin 3, ∀ v, claimNoun d.c k = .atom v → v < P → x[2 * k.val]! = 0 ∧ x[2 * k.val + 1]! = UInt64.ofNat v)
    (hcl : ∀ k : Fin 3, isCellN (claimNoun d.c k) = true → SP.labelOf x (2 * k.val) = 1)
    (hbg : ∀ k : Fin 3, isBigN P (claimNoun d.c k) = true → SP.labelOf x (2 * k.val) = 2)
    (χ : Nock.NockVMROM.Thm54.SVFrame.Coins FrameJ8.frameJ8 KN)
    (h13 : χ ⟨13, (by norm_num : 13 < 19)⟩ = toKV coins[13]!) (h14 : χ ⟨14, (by norm_num : 14 < 19)⟩ = toKV coins[14]!) :
    ∀ j : Fin 33, zP x[j.val]! = pubVJ9 deltaF Nock.TraceGenExe.powerBasis3 d.c (mOf x) (ρOf x) (ρSOf x) χ j.val := by
  obtain ⟨-, hα, hsd, h12, h13', h14', -⟩ := hder
  have hcx : ∀ a b c : ℕ, canon3 (⟨x[a]!, x[b]!, x[c]!⟩ : VF.K3) := fun a b c => ⟨hx a, hx b, hx c⟩
  have hseed : seedJ9 (p := P) d.c (mOf x) (FrameVSQ.toVS (FrameJ8.toVSQ χ)) = toKV ⟨x[9]!, x[10]!, x[11]!⟩ := by
    unfold seedJ9
    refine (seed_eq9 d x hat hcl hbg _ _).trans ?_
    show χ ⟨13, _⟩ * ∑ q : Fin 6, (χ ⟨14, _⟩) ^ (q : ℕ) * algebraMap (ZMod P) KN (zP x[q.val]!) = _
    rw [h13, h14, hsd]
    congr 1
  rintro ⟨j, hj⟩
  show zP x[j]! = _
  unfold pubVJ9
  by_cases c1 : j < 6
  · rw [if_pos c1]; exact (labelJ9_get d x hat hcl hbg j c1).symm
  rw [if_neg c1]
  by_cases c3 : 9 ≤ j ∧ j < 12
  · rw [dif_pos c3, hseed, coord_toKV _ (hcx 9 10 11)]
    obtain ⟨c3a, c3b⟩ := c3
    interval_cases j <;> rfl
  rw [dif_neg c3]
  unfold VerJ8.pubVJ8 FrameVSQ.pubVHQ FrameVS.pubVH
  dsimp only
  have hr3 : ρOf x 3 = φ (SP.qmk (SP.pubK x 5) (SP.pubK x 7)) := by unfold ρOf; rw [rhoOf3]
  have hr4 : ρOf x 4 = φ (SP.qmk (SP.pubK x 6) (SP.pubK x 8)) := by unfold ρOf; rw [rhoOf4]
  have h27 : j < 27 ∨ 27 ≤ j := by omega
  rcases h27 with h27 | h27
  · rw [if_pos h27]
    by_cases h21 : j < 21
    · rw [if_pos h21, if_neg c1]
      by_cases c2 : j < 9
      · rw [dif_pos c2]
        show zP x[j]! = Nock.NockVMROM.Thm54.CoordinateBasis.coord _ (χ ⟨13, _⟩) _
        rw [h13, ← hα, coord_toKV _ (hcx 6 7 8)]
        interval_cases j <;> rfl
      rw [dif_neg c2]
      by_cases c3' : j < 12
      · exfalso; omega
      rw [dif_neg c3']
      by_cases c4 : j < 15
      · rw [if_pos c4]
        have hz0 : ∀ g : UInt64, g = 0 → zP g = 0 := fun g hg => by subst hg; rfl
        interval_cases j
        · exact hz0 _ h12
        · exact hz0 _ h13'
        · exact hz0 _ h14'
      rw [if_neg c4]
      by_cases c5 : j < 18
      · rw [dif_pos c5, hr3, re_φ, coord_pubK x hx 5]
        interval_cases j <;> rfl
      · rw [dif_neg c5, dif_pos h21, hr4, re_φ, coord_pubK x hx 6]
        interval_cases j <;> rfl
    · rw [if_neg h21]
      by_cases d1 : j < 24
      · rw [dif_pos d1, hr3, im_φ, coord_pubK x hx 7]
        interval_cases j <;> rfl
      · rw [dif_neg d1, dif_pos h27, hr4, im_φ, coord_pubK x hx 8]
        interval_cases j <;> rfl
  · rw [if_neg (by omega : ¬ j < 27)]
    have hrS : ρSOf x = φ (SP.qmk (SP.pubK x 9) (SP.pubK x 10)) := rfl
    by_cases e1 : j < 30
    · rw [dif_pos e1, hrS, re_φ, coord_pubK x hx 9]
      interval_cases j <;> rfl
    · rw [dif_neg e1, dif_pos (by omega : j < 33), hrS, im_φ, coord_pubK x hx 10]
      interval_cases j <;> rfl


/-! ### records and the public equations -/

open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8P (pinRecsJ8)

theorem claimCellRecs_eq9 (d : Datum9A) (hclR : ∀ k : Fin 3, isCellN (claimNoun d.c k) = true → (claimNoun d.c k).internal / 2 ^ 62 < P)
    (z y : PE.K6) (hz : SP.canon6 z) (hy : SP.canon6 y)
    (χ : Nock.NockVMROM.Thm54.SVFrame.Coins FrameJ8.frameJ8 KN) (hzψ : ψ z = Quad.mk δK (χ Nock.NockVMROM.Thm54.VclL.Handle.WeightsJ8.c2) (χ Nock.NockVMROM.Thm54.VclL.Handle.WeightsJ8.c3))
    (hyψ : ψ y = Quad.mk δK (χ FrameJ8.cY1) (χ FrameJ8.cY2)) (x : Array UInt64) (hx : SP.ArrCan x) :
    ((claimCells d.c).map fun k => PE.claimVec (fpOf z z.inv0 y (claimNoun d.c k)) (SP.labelOf x (2 * k.val + 1))
        (rkC (claimNoun d.c k)).1 (rkC (claimNoun d.c k)).2).map (fun r => fun c : Fin 5 => φ (SP.recQ r c)) =
      AcceptsJ8P.claimRecsJ8 (K := KN) deltaF χ d.c (fun k => (x[2 * k.val + 1]!.toNat, 0, 0)) := by
  unfold AcceptsJ8P.claimRecsJ8
  rw [List.map_map]
  refine List.map_congr_left fun k hk => ?_
  have hcell : isCellN (claimNoun d.c k) = true := by
    unfold claimCells at hk
    exact (List.mem_filter.1 hk).2
  have hrk := hclR k hcell
  have hlab : SP.labelOf x (2 * k.val + 1) < 18446744073709551616 := by
    have := hx (2 * k.val + 1)
    unfold SP.labelOf canon at *
    have h2 := P_lt
    have h3 : NockvmE2E.Exec.p = P := rfl
    omega
  have hhi : (rkC (claimNoun d.c k)).1 < 18446744073709551616 := lt_trans hrk P_lt
  have hlo : (rkC (claimNoun d.c k)).2 < 18446744073709551616 := by
    have : (rkC (claimNoun d.c k)).2 < 2 ^ 62 := Nat.mod_lt _ (by norm_num)
    omega
  have e1 := claimVec_spec (fpOf z z.inv0 y (claimNoun d.c k)) (SP.labelOf x (2 * k.val + 1)) _ _ hlab hhi hlo
  have e2 := encZY_spec z y hz hy (claimNoun d.c k)
  rw [hzψ, hyψ] at e2
  show (fun c : Fin 5 => ψ ((PE.claimVec _ _ _ _).getD c PE.K6.zero)) = _
  rw [e1, e2]
  rfl

theorem claimBigRecs_eq9 (d : Datum9A) (z y : PE.K6) (hz : SP.canon6 z) (hy : SP.canon6 y)
    (χ : Nock.NockVMROM.Thm54.SVFrame.Coins FrameJ8.frameJ8 KN) (hzψ : ψ z = Quad.mk δK (χ Nock.NockVMROM.Thm54.VclL.Handle.WeightsJ8.c2) (χ Nock.NockVMROM.Thm54.VclL.Handle.WeightsJ8.c3))
    (hyψ : ψ y = Quad.mk δK (χ FrameJ8.cY1) (χ FrameJ8.cY2)) (x : Array UInt64) (hx : SP.ArrCan x) :
    ((claimBigs P d.c).map fun k => PE.claimVec (fpOf z z.inv0 y (claimNoun d.c k)) (SP.labelOf x (2 * k.val + 1)) 0 0).map
        (fun r => fun c : Fin 5 => φ (SP.recQ r c)) =
      claimBigRecs (p := P) deltaF χ d.c (mOf x) := by
  unfold claimBigRecs
  rw [List.map_map]
  refine List.map_congr_left fun k hk => ?_
  have hlab : SP.labelOf x (2 * k.val + 1) < 18446744073709551616 := by
    have := hx (2 * k.val + 1)
    unfold SP.labelOf canon at *
    have h2 := P_lt
    have h3 : NockvmE2E.Exec.p = P := rfl
    omega
  have e1 := claimVec_spec (fpOf z z.inv0 y (claimNoun d.c k)) (SP.labelOf x (2 * k.val + 1)) 0 0 hlab (by norm_num) (by norm_num)
  have e2 := encZY_spec z y hz hy (claimNoun d.c k)
  rw [hzψ, hyψ] at e2
  show (fun c : Fin 5 => ψ ((PE.claimVec _ _ _ _).getD c PE.K6.zero)) = _
  rw [e1, e2]
  simp only [Nat.cast_zero]
  rfl

theorem pinRecs9_eq (d : Datum9A) (hlt : ∀ id ∈ d.Pb.regs, (d.Pb.rk id).1 < ringChar (ZMod P) ∧ (d.Pb.rk id).2 < ringChar (ZMod P) ∧
      d.Pb.idx id < ringChar (ZMod P)) (z y : PE.K6) (hz : SP.canon6 z) (hy : SP.canon6 y)
    (χ : Nock.NockVMROM.Thm54.SVFrame.Coins FrameJ8.frameJ8 KN)
    (hzψ : ψ z = Quad.mk δK (χ Nock.NockVMROM.Thm54.VclL.Handle.WeightsJ8.c2) (χ Nock.NockVMROM.Thm54.VclL.Handle.WeightsJ8.c3))
    (hyψ : ψ y = Quad.mk δK (χ FrameJ8.cY1) (χ FrameJ8.cY2)) :
    (d.Pb.regs.map fun id => PE.claimVec (fpOf z z.inv0 y (Nock.Jet.Autogen.compile P (d.Pb.Rt id))) (d.Pb.idx id)
        (d.Pb.rk id).1 (d.Pb.rk id).2).map (fun r => fun c : Fin 5 => φ (SP.recQ r c)) =
      pinRecsJ8 (K := KN) deltaF d.Pb.toPubJ8 χ := by
  unfold AcceptsJ8P.pinRecsJ8
  rw [List.map_map]
  refine List.map_congr_left fun id hid => ?_
  have hl := hlt id hid
  rw [ringChar_P] at hl
  have hi : d.Pb.idx id < 18446744073709551616 := lt_trans hl.2.2 P_lt
  have hh : (d.Pb.rk id).1 < 18446744073709551616 := lt_trans hl.1 P_lt
  have hlo : (d.Pb.rk id).2 < 18446744073709551616 := lt_trans hl.2.1 P_lt
  have e1 := claimVec_spec (fpOf z z.inv0 y (Nock.Jet.Autogen.compile P (d.Pb.Rt id))) (d.Pb.idx id) _ _ hi hh hlo
  have e2 := encZY_spec z y hz hy (Nock.Jet.Autogen.compile P (d.Pb.Rt id))
  rw [hzψ, hyψ] at e2
  show (fun c : Fin 5 => ψ ((PE.claimVec _ _ _ _).getD c PE.K6.zero)) = _
  rw [e1, e2]

set_option maxHeartbeats 1600000 in
theorem pubEq9_of_P (d : Datum9A) (hS : StmtP9A d) (inp : PE.PubIn) (hlink : InpLink9 d inp) (L : PE.PubLayout)
    (slotOf : Array ℕ) (slots : Array VF.K3) (pub : Array UInt64) (hs : ∀ s ∈ slots, canon3 s) (hp : ∀ g ∈ pub, canon g)
    (hids : ∀ id ∈ d.Pb.regs, id < P)
    (χ : Nock.NockVMROM.Thm54.SVFrame.Coins FrameJ8.frameJ8 KN) (hχ : ∀ i : Fin 19, χ i = toKV (SP.coinsOf slots slotOf)[i.val]!)
    (hP : PubJ9P inp L slotOf slots pub) :
    NockvmE2E.J9A.InstJ9A.PubEq9A d χ (Mof9 L pub) := by
  obtain ⟨cr, pr, hcr, hpr, hrel⟩ := hP.1
  have hc := coinsOf_can slots slotOf hs
  have hx : SP.ArrCan (SP.slOf L pub 0) := SP.slOf_can L pub hp 0
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hrel
  have hz : SP.canon6 ⟨(SP.coinsOf slots slotOf)[2]!, (SP.coinsOf slots slotOf)[3]!⟩ := ⟨hc 2, hc 3⟩
  have hy : SP.canon6 ⟨(SP.coinsOf slots slotOf)[17]!, (SP.coinsOf slots slotOf)[18]!⟩ := ⟨hc 17, hc 18⟩
  have hzψ : ψ ⟨(SP.coinsOf slots slotOf)[2]!, (SP.coinsOf slots slotOf)[3]!⟩ =
      Quad.mk δK (χ Nock.NockVMROM.Thm54.VclL.Handle.WeightsJ8.c2) (χ Nock.NockVMROM.Thm54.VclL.Handle.WeightsJ8.c3) := by
    have e2 : χ Nock.NockVMROM.Thm54.VclL.Handle.WeightsJ8.c2 = toKV (SP.coinsOf slots slotOf)[2]! := hχ ⟨2, (by norm_num : 2 < 19)⟩
    have e3 : χ Nock.NockVMROM.Thm54.VclL.Handle.WeightsJ8.c3 = toKV (SP.coinsOf slots slotOf)[3]! := hχ ⟨3, (by norm_num : 3 < 19)⟩
    rw [e2, e3]; rfl
  have hyψ : ψ ⟨(SP.coinsOf slots slotOf)[17]!, (SP.coinsOf slots slotOf)[18]!⟩ =
      Quad.mk δK (χ Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8.cY1) (χ Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8.cY2) := by
    have e2 : χ Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8.cY1 = toKV (SP.coinsOf slots slotOf)[17]! := hχ ⟨17, (by norm_num : 17 < 19)⟩
    have e3 : χ Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8.cY2 = toKV (SP.coinsOf slots slotOf)[18]! := hχ ⟨18, (by norm_num : 18 < 19)⟩
    rw [e2, e3]; rfl
  -- the records
  rw [hlink.hcl] at hcr
  have hcells : ∀ k ∈ claimCells d.c, isCellN (claimNoun d.c k) = true := fun k hk => by
    unfold claimCells at hk; exact (List.mem_filter.1 hk).2
  have hbigs : ∀ k ∈ claimBigs P d.c, isBigN P (claimNoun d.c k) = true := fun k hk => by
    unfold claimBigs at hk; exact (List.mem_filter.1 hk).2
  obtain ⟨ra, rb, hra, hrb, hcr_eq⟩ := mapM_append_some _ _ _ _ hcr
  obtain ⟨-, hra'⟩ := claims_mapM _ _ (SP.slOf L pub 0) (claimNoun d.c) (claimCells d.c) hcells ra hra
  obtain ⟨-, hrb'⟩ := claims_mapM_big _ _ (SP.slOf L pub 0) (claimNoun d.c) (claimBigs P d.c) hbigs rb hrb
  have hpm := pins_mapM ⟨(SP.coinsOf slots slotOf)[2]!, (SP.coinsOf slots slotOf)[3]!⟩
    ⟨(SP.coinsOf slots slotOf)[17]!, (SP.coinsOf slots slotOf)[18]!⟩ (fun id => Nock.Jet.Autogen.compile P (d.Pb.Rt id))
    d.Pb.idx (fun id => (d.Pb.rk id).1) (fun id => (d.Pb.rk id).2) d.Pb.regs
  rw [hlink.hpin] at hpr
  have hpr'' := Option.some.inj (hpr.symm.trans hpm)
  have hb : ∀ id ∈ d.Pb.regs, id < 18446744073709551616 ∧ d.Pb.idx id < 18446744073709551616 := fun id hid =>
    ⟨lt_trans (hids id hid) P_lt, by have := (hS.hlt id hid).2.2; rw [ringChar_P] at this; exact lt_trans this P_lt⟩
  have hg : FrameVSQ.gamHQ deltaF (FrameJ8.toVSQ χ) = φ (SP.qmk (toKV (SP.coinsOf slots slotOf)[11]!) (toKV (SP.coinsOf slots slotOf)[15]!)) := by
    have e2 : χ ⟨11, (by norm_num : 11 < 19)⟩ = toKV (SP.coinsOf slots slotOf)[11]! := hχ ⟨11, (by norm_num : 11 < 19)⟩
    have e3 : χ ⟨15, (by norm_num : 15 < 19)⟩ = toKV (SP.coinsOf slots slotOf)[15]! := hχ ⟨15, (by norm_num : 15 < 19)⟩
    show Quad.mk _ (χ ⟨11, _⟩) (χ ⟨15, _⟩) = _
    rw [e2, e3]; rfl
  have hr : FrameVSQ.rhoHQ deltaF (FrameJ8.toVSQ χ) = φ (SP.qmk (toKV (SP.coinsOf slots slotOf)[12]!) (toKV (SP.coinsOf slots slotOf)[16]!)) := by
    have e2 : χ ⟨12, (by norm_num : 12 < 19)⟩ = toKV (SP.coinsOf slots slotOf)[12]! := hχ ⟨12, (by norm_num : 12 < 19)⟩
    have e3 : χ ⟨16, (by norm_num : 16 < 19)⟩ = toKV (SP.coinsOf slots slotOf)[16]! := hχ ⟨16, (by norm_num : 16 < 19)⟩
    show Quad.mk _ (χ ⟨12, _⟩) (χ ⟨16, _⟩) = _
    rw [e2, e3]; rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, h6, h7, h8⟩
  · have e := congrArg φ h1
    rw [map_add, map_add, φ_mk, φ_mk, φ_mk] at e
    exact e
  · have e := congrArg φ h2
    rw [map_add, φ_mk, φ_mk] at e
    exact e
  · have hpc : (inp.pins.map fun q => (SP.recQ (PE.pinConsKey q.key q.idx) : Fin 8 → SP.Q)) =
        d.Pb.regs.map fun id => SP.recQ (PE.pinConsKey id (d.Pb.idx id)) := by
      rw [hlink.hpin, List.map_map]; rfl
    rw [hpc] at h3
    have e := congrArg φ h3
    simp only [map_add] at e
    rw [inv_comp, pinConsR_eq _ _ hb, List.map_map] at e
    rw [VerJ8.coinsCV_J8, hg, hr]
    exact e
  · have e4 : χ Nock.NockVMROM.Thm54.VclL.Handle.WeightsJ8.c4 = toKV (SP.coinsOf slots slotOf)[4]! := hχ ⟨4, (by norm_num : 4 < 19)⟩
    have e5 : χ Nock.NockVMROM.Thm54.VclL.Handle.WeightsJ8.c5 = toKV (SP.coinsOf slots slotOf)[5]! := hχ ⟨5, (by norm_num : 5 < 19)⟩
    have e6 : χ Nock.NockVMROM.Thm54.VclL.Handle.WeightsJ8.c6 = toKV (SP.coinsOf slots slotOf)[6]! := hχ ⟨6, (by norm_num : 6 < 19)⟩
    have e7 : χ Nock.NockVMROM.Thm54.VclL.Handle.WeightsJ8.c7 = toKV (SP.coinsOf slots slotOf)[7]! := hχ ⟨7, (by norm_num : 7 < 19)⟩
    have hmap : ∀ (l : List (List PE.K6)), (l.map fun r => (SP.recQ r : Fin 5 → SP.Q)).map (fun r c => φ (r c)) =
        l.map (fun r => fun c : Fin 5 => φ (SP.recQ r c)) := by
      intro l; rw [List.map_map]; rfl
    have e := congrArg φ h4
    rw [map_add, inv_comp, List.map_append, hmap, hmap, hcr_eq, hra', hrb'] at e
    rw [hpr''] at e
    simp only [List.map_append] at e
    rw [claimCellRecs_eq9 d hS.hclR _ _ hz hy χ hzψ hyψ _ hx, claimBigRecs_eq9 d _ _ hz hy χ hzψ hyψ _ hx,
      pinRecs9_eq d hS.hlt _ _ hz hy χ hzψ hyψ] at e
    rw [e4, e5, e6, e7]
    unfold claimRecsJ9
    rw [List.map_append, List.map_append]
    exact e
  · have e := congrArg φ h5
    rw [map_add, φ_mk, φ_mk, φ_mk] at e
    exact e


/-! ### `hRVU_J9A` -/

set_option maxHeartbeats 800000 in
/-- **`hRVU_J9A`: the public twin at J-9 A.**  The verifier-side relation `PubJ9P` gives nock's `PubP9A d χ` at the message
`Mof9 L pub`.  Hypotheses as `hRVU_J8` (`StmtP9A`, the datum link `InpLink9`, canonical slots / publics, registry ids `< p`, the coins
are the slot coins) and, for each optional table (jet, atom walk, axis, split), that an absent one has `present = false`. -/
theorem hRVU_J9A (d : Datum9A) (hS : StmtP9A d) (inp : PE.PubIn) (hlink : InpLink9 d inp) (L : PE.PubLayout)
    (slotOf : Array ℕ) (slots : Array VF.K3) (pub : Array UInt64) (hs : ∀ s ∈ slots, canon3 s) (hp : ∀ g ∈ pub, canon g)
    (hids : ∀ id ∈ d.Pb.regs, id < P)
    (hpJ : d.Pb.nJ = 0 → L.present[3]! = false) (hpV : d.Pb.krootsV = 0 → L.present[5]! = false)
    (hpX : d.Pb.axOn = false → L.present[6]! = false) (hpS : d.Pb.spOn = false → L.present[7]! = false)
    (χ : NockvmE2E.Rap.Coins Φ0 KN) (hχ : ∀ i : Fin 19, χ i = toKV (SP.coinsOf slots slotOf)[i.val]!)
    (hP : PubJ9P inp L slotOf slots pub) :
    PubP9A d χ (Mof9 L pub) := by
  have hP' := hP
  obtain ⟨⟨cr, pr, hcr, hpr, hrel⟩, hder⟩ := hP
  have hx : SP.ArrCan (SP.slOf L pub 0) := SP.slOf_can L pub hp 0
  have hcells : ∀ k ∈ claimCells d.c, isCellN (claimNoun d.c k) = true := fun k hk => by
    unfold claimCells at hk; exact (List.mem_filter.1 hk).2
  have hbigs : ∀ k ∈ claimBigs P d.c, isBigN P (claimNoun d.c k) = true := fun k hk => by
    unfold claimBigs at hk; exact (List.mem_filter.1 hk).2
  rw [hlink.hcl] at hcr
  obtain ⟨ra, rb, hra, hrb, -⟩ := mapM_append_some _ _ _ _ hcr
  obtain ⟨hcl0, -⟩ := claims_mapM _ _ (SP.slOf L pub 0) (claimNoun d.c) (claimCells d.c) hcells ra hra
  obtain ⟨hbg0, -⟩ := claims_mapM_big _ _ (SP.slOf L pub 0) (claimNoun d.c) (claimBigs P d.c) hbigs rb hrb
  have hcl : ∀ k : Fin 3, isCellN (claimNoun d.c k) = true → SP.labelOf (SP.slOf L pub 0) (2 * k.val) = 1 := by
    intro k hk
    exact hcl0 k (by unfold claimCells; exact List.mem_filter.2 ⟨List.mem_finRange k, hk⟩)
  have hbg : ∀ k : Fin 3, isBigN P (claimNoun d.c k) = true → SP.labelOf (SP.slOf L pub 0) (2 * k.val) = 2 := by
    intro k hk
    exact hbg0 k (by unfold claimBigs; exact List.mem_filter.2 ⟨List.mem_finRange k, hk⟩)
  have hat : ∀ k : Fin 3, ∀ v, claimNoun d.c k = .atom v → v < P →
      (SP.slOf L pub 0)[2 * k.val]! = 0 ∧ (SP.slOf L pub 0)[2 * k.val + 1]! = UInt64.ofNat v := by
    intro k v hk hv
    have hmem : (k.val, v) ∈ inp.atoms := by
      rw [hlink.hat]
      exact List.mem_filterMap.2 ⟨k, List.mem_finRange k, by simp [hk, not_le.2 hv]⟩
    exact (hder.2.2.2.2.2.2 _ hmem).2
  refine ⟨pubEq9_of_P d hS inp hlink L slotOf slots pub hs hp hids χ hχ hP', ?_, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · intro k _
    exact hx (2 * k.val + 1)
  · intro hV
    have : SP.slOf L pub 5 = Array.replicate L.lens[5]! 0 := by
      unfold SP.slOf; rw [if_neg (by simp [hpV hV])]
    show SP.pubK (SP.slOf L pub 5) 0 = 0 ∧ SP.pubK (SP.slOf L pub 5) 1 = 0 ∧ SP.pubK (SP.slOf L pub 5) 4 = 0 ∧
      SP.pubK (SP.slOf L pub 5) (4 + 1) = 0 ∧ SP.pubK (SP.slOf L pub 5) 6 = 0 ∧ SP.pubK (SP.slOf L pub 5) (6 + 1) = 0
    rw [this]
    exact ⟨pubK_replicate _ _, pubK_replicate _ _, pubK_replicate _ _, pubK_replicate _ _, pubK_replicate _ _, pubK_replicate _ _⟩
  · intro hJ
    have : SP.slOf L pub 3 = Array.replicate L.lens[3]! 0 := by
      unfold SP.slOf; rw [if_neg (by simp [hpJ hJ])]
    show SP.pubK (SP.slOf L pub 3) 0 = 0 ∧ SP.pubK (SP.slOf L pub 3) 1 = 0 ∧ SP.pubK (SP.slOf L pub 3) 2 = 0 ∧
      SP.pubK (SP.slOf L pub 3) 3 = 0
    rw [this]
    exact ⟨pubK_replicate _ _, pubK_replicate _ _, pubK_replicate _ _, pubK_replicate _ _⟩
  · intro hX
    have : SP.slOf L pub 6 = Array.replicate L.lens[6]! 0 := by
      unfold SP.slOf; rw [if_neg (by simp [hpX hX])]
    show SP.pubK (SP.slOf L pub 6) 0 = 0 ∧ SP.pubK (SP.slOf L pub 6) (0 + 1) = 0 ∧ SP.pubK (SP.slOf L pub 6) 2 = 0 ∧
      SP.pubK (SP.slOf L pub 6) (2 + 1) = 0
    rw [this]
    exact ⟨pubK_replicate _ _, pubK_replicate _ _, pubK_replicate _ _, pubK_replicate _ _⟩
  · intro hSp
    have : SP.slOf L pub 7 = Array.replicate L.lens[7]! 0 := by
      unfold SP.slOf; rw [if_neg (by simp [hpS hSp])]
    show SP.pubK (SP.slOf L pub 7) 0 = 0 ∧ SP.pubK (SP.slOf L pub 7) (0 + 1) = 0
    rw [this]
    exact ⟨pubK_replicate _ _, pubK_replicate _ _⟩
  · exact derived9_of d inp _ hx _ hder hat hcl hbg χ (hχ ⟨13, (by norm_num : 13 < 19)⟩) (hχ ⟨14, (by norm_num : 14 < 19)⟩)

end NockvmE2E.J9A.RVUJ9A

#print axioms NockvmE2E.J9A.RVUJ9A.pubCheck9_sound
#print axioms NockvmE2E.J9A.RVUJ9A.claims_mapM_big
#print axioms NockvmE2E.J9A.RVUJ9A.derived9_of
#print axioms NockvmE2E.J9A.RVUJ9A.pubEq9_of_P
#print axioms NockvmE2E.J9A.RVUJ9A.hRVU_J9A
