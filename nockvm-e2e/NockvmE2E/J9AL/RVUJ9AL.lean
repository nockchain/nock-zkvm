/-
the J-9 AL twin of `J9A/RVUJ9A.lean`.
 * §1 `primRecS`, `PrimsCan`, `PubJ9LRel` (the eight conjuncts of nock `PubEq9AL`, with `ρ`, `ρS` as data), `checkPubEq9L_sound`,
   `PubJ9LP`, `pubCheck9L_sound` (twins of `checkPubEq9_sound`, `PubJ9P`, `pubCheck9_sound`: nine tables, the primitive records).
 * §2 the record lemmas and `hRVU_J9AL` (`PubJ9LP` gives nock's `PubP9AL d χ (Mof9L L pub)`).
Not zero-knowledge.
-/
import NockvmE2E.J9AL.InstJ9AL
import NockvmE2E.J9A.RVUJ9A
import NockvmE2E.Exec.PubExe9L
import NockvmE2E.Exec.PrimToksTie

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option pp.deepTerms false
set_option pp.maxSteps 2000

namespace NockvmE2E.J9AL.RVUJ9AL

open NockvmE2E.Exec NockvmE2E.Exec.SP NockvmE2E.Exec.VL
open NockvmE2E.J9A.RVUJ9A

/-! ## 1. The relation and the soundness of the executable check -/

/-- the primitive record of the verifier: `claimVec (enc (primToks code)) idx hi lo` -/
def primRecS (z y : PE.K6) (q : PE.PrimRec) : Option (List PE.K6) := do
  let e ← PE.enc z y (← PE.primToks q.code)
  pure (PE.claimVec e q.idx q.hi q.lo)

/-- the primitive table's numbers are canonical field elements -/
def PrimsCan (inp : PE.PubIn) : Prop :=
  ∀ q ∈ inp.prims, q.id < VF.PN ∧ q.code < VF.PN ∧ q.idx < VF.PN ∧ q.hi < VF.PN ∧ q.lo < VF.PN

theorem primRecS_can (z y : PE.K6) (hz : canon6 z) (hy : canon6 y) (q : PE.PrimRec) (hi : q.idx < VF.PN)
    (hhi : q.hi < VF.PN) (hlo : q.lo < VF.PN) (r : List PE.K6) (h : primRecS z y q = some r) :
    r.length = 5 ∧ ∀ w ∈ r, canon6 w := by
  unfold primRecS at h
  rcases ht : PE.primToks q.code with _ | t
  · simp [ht] at h
  rcases he : PE.enc z y t with _ | e
  · simp [ht, he] at h
  simp only [ht, he, bind, Option.bind, pure, Option.some.injEq] at h
  subst h
  exact ⟨rfl, canon6_claimVec e (enc_can z y hz hy _ e he) _ _ _ hi hhi hlo⟩

/-- an eight-entry key of small numbers is canonical -/
theorem keys8_can (l : List ℕ) (hl : l.length = 8) (h : ∀ a ∈ l, a < VF.PN) :
    (l.map fun v => PE.K6.base (UInt64.ofNat v)).length = 8 ∧
      ∀ w ∈ (l.map fun v => PE.K6.base (UInt64.ofNat v)), canon6 w := by
  refine ⟨by simpa using hl, ?_⟩
  intro w hw
  obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hw
  exact canon6_base _ (canon_ofNat a (h a ha))

theorem pinRgKey_can (id idx : ℕ) (hid : id < VF.PN) (hidx : idx < VF.PN) :
    (PE.pinRgKey id idx).length = 8 ∧ ∀ w ∈ PE.pinRgKey id idx, canon6 w := by
  refine keys8_can [id, 1, idx, 0, 0, 0, 0, 7] rfl ?_
  intro a ha
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at ha
  unfold VF.PN at *
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega

theorem pinOpKey_can (id code : ℕ) (hid : id < VF.PN) (hcode : code < VF.PN) :
    (PE.pinOpKey id code).length = 8 ∧ ∀ w ∈ PE.pinOpKey id code, canon6 w := by
  refine keys8_can [id, code, 0, 0, 0, 0, 0, 6] rfl ?_
  intro a ha
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at ha
  unfold VF.PN at *
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega

/-- the eight conjuncts of `PubEq9AL` over the verifier's data (cf. `PubJ9Rel`): `hGx` gains the ALU export terminal (`pubALx = 4`), `hGS`
the two pin sums `pinRg`, `pinOp` (grouped `Σ pinRg + Σ pinOp`, as the executable) and the ALU service terminal (`pubALs = 2`), `hsumC'`
the ALU validity terminal (`pubALv = 0`) and the primitive records -/
noncomputable def PubJ9LRel (χ : Fin 19 → KC) (ρ : Fin 5 → Q) (ρS : Q)
    (pubsC pubsW pubsJ pubsA pubsV pubsX pubsS pubsL : ℕ → KC)
    (pinConsR pinRgR pinOpR : List (Fin 8 → Q)) (claimRecs pinRecs primRecs : List (Fin 5 → Q)) : Prop :=
  (ρ 3 + (qmk (pubsW 4) (pubsW (4 + 1)) + qmk (pubsJ 2) (pubsJ 3) + qmk (pubsL 4) (pubsL (4 + 1))) =
    qmk (pubsC 4) (pubsC (4 + 1))) ∧
  (ρ 4 + qmk (pubsX 2) (pubsX (2 + 1)) = qmk (pubsW 6) (pubsW (6 + 1))) ∧
  (ρS + (pinConsR.map fun r => qinv (compressQ (qmk (χ 11) (χ 15)) (qmk (χ 12) (χ 16)) r)).sum +
      ((pinRgR.map fun r => qinv (compressQ (qmk (χ 11) (χ 15)) (qmk (χ 12) (χ 16)) r)).sum +
        (pinOpR.map fun r => qinv (compressQ (qmk (χ 11) (χ 15)) (qmk (χ 12) (χ 16)) r)).sum)
      + qmk (pubsJ 0) (pubsJ 1) + qmk (pubsX 0) (pubsX (0 + 1)) + qmk (pubsL 2) (pubsL (2 + 1)) =
    qmk (pubsA 8) (pubsA (8 + 1)) + qmk (pubsV 6) (pubsV (6 + 1)) + qmk (pubsS 0) (pubsS (0 + 1))) ∧
  (qmk (pubsL 0) (pubsL (0 + 1)) +
      ((claimRecs ++ pinRecs ++ primRecs).map fun r => qinv (compressQ (m := 5) (qmk (χ 4) (χ 6)) (qmk (χ 5) (χ 7)) r)).sum =
    qmk (pubsC 0) (pubsC 1) + qmk (pubsA 6) (pubsA (6 + 1))) ∧
  (qmk (pubsA 4) (pubsA (4 + 1)) = qmk (pubsA 10) (pubsA (10 + 1)) + qmk (pubsV 4) (pubsV (4 + 1))) ∧
  (pubsA 0 = 0 ∧ pubsA 1 = 0) ∧
  (pubsC 2 = pubsW 0 ∧ pubsC 3 = pubsW 1) ∧
  (pubsA 2 = pubsV 0 ∧ pubsA 3 = pubsV 1)

section Main
open PE

theorem checkPubEq9L_sound (inp : PubIn) (coins : Array VF.K3) (ps : PubSet9) (al : Array UInt64)
    (hc : ∀ i : ℕ, canon3 coins[i]!)
    (h0 : ArrCan ps.compute) (h1 : ArrCan ps.cell) (h2 : ArrCan ps.walkJ8) (h3 : ArrCan ps.jet)
    (h4 : ArrCan ps.atom) (h5 : ArrCan ps.walkAtom) (h6 : ArrCan ps.axis) (h7 : ArrCan ps.split) (h8 : ArrCan al)
    (hinp : InpCan inp) (hP : PrimsCan inp)
    (h : checkPubEq9L inp coins ps al = true) :
    (∃ cr pr qr : List (List K6),
      inp.claimCells.mapM (claimRecS ⟨coins[2]!, coins[3]!⟩ ⟨coins[17]!, coins[18]!⟩ ps.compute) = some cr ∧
      inp.pins.mapM (pinRecS ⟨coins[2]!, coins[3]!⟩ ⟨coins[17]!, coins[18]!⟩) = some pr ∧
      inp.prims.mapM (primRecS ⟨coins[2]!, coins[3]!⟩ ⟨coins[17]!, coins[18]!⟩) = some qr ∧
      PubJ9LRel (fun i : Fin 19 => toKV coins[(i : ℕ)]!) (rhoOf ps.compute) (rhoSOf ps.compute) (pubK ps.cell)
        (pubK ps.walkJ8) (pubK ps.jet) (pubK ps.atom) (pubK ps.walkAtom) (pubK ps.axis) (pubK ps.split) (pubK al)
        (inp.pins.map fun q => (recQ (PE.pinConsKey q.key q.idx) : Fin 8 → Q))
        (inp.prims.map fun q => (recQ (PE.pinRgKey q.id q.idx) : Fin 8 → Q))
        (inp.prims.map fun q => (recQ (PE.pinOpKey q.id q.code) : Fin 8 → Q))
        (cr.map fun r => (recQ r : Fin 5 → Q)) (pr.map fun r => (recQ r : Fin 5 → Q))
        (qr.map fun r => (recQ r : Fin 5 → Q))) ∧
      ComputeDerivedP inp coins ps.compute := by
  unfold checkPubEq9L at h
  simp only [] at h
  split at h
  · simp at h
  have h := getD_true h
  obtain ⟨cr, hcr, h⟩ := bind_some h
  obtain ⟨pr, hpr, h⟩ := bind_some h
  obtain ⟨qr, hqr, h⟩ := bind_some h
  obtain ⟨w0, hw0, h⟩ := bind_some h
  obtain ⟨j2, hj2, h⟩ := bind_some h
  obtain ⟨ch, hch, h⟩ := bind_some h
  obtain ⟨w1, hw1, h⟩ := bind_some h
  obtain ⟨axp, haxp, h⟩ := bind_some h
  obtain ⟨axs, haxs, h⟩ := bind_some h
  obtain ⟨sps, hsps, h⟩ := bind_some h
  obtain ⟨alv, halv, h⟩ := bind_some h
  obtain ⟨als, hals, h⟩ := bind_some h
  obtain ⟨alx, halx, h⟩ := bind_some h
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
  have hqr' : inp.prims.mapM (primRecS ⟨coins[2]!, coins[3]!⟩ ⟨coins[17]!, coins[18]!⟩) = some qr := hqr
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
  have hqrc : ∀ r ∈ qr, r.length = 5 ∧ ∀ w ∈ r, canon6 w := by
    intro r hr
    obtain ⟨q, hqm, hqc⟩ := mapM_mem _ _ _ hqr' r hr
    have := hP q hqm
    exact primRecS_can _ _ hz hy q this.2.2.1 this.2.2.2.1 this.2.2.2.2 r hqc
  refine ⟨⟨cr, pr, qr, hcr', hpr', hqr', ?_⟩, computeDerivedOk_sound inp coins ps.compute hc h0 e0⟩
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
  obtain ⟨calv, talv⟩ := pp_some _ h8 _ _ halv
  obtain ⟨cals, tals⟩ := pp_some _ h8 _ _ hals
  obtain ⟨calx, talx⟩ := pp_some _ h8 _ _ halx
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
  have hrg := foldl_invSum (fun q : PrimRec => PE.compress ⟨coins[11]!, coins[15]!⟩ ⟨coins[12]!, coins[16]!⟩
    (PE.pinRgKey q.id q.idx)) inp.prims K6.zero canon6_zero
  have hrgq : (inp.prims.map fun q => qinv (toQ6 (PE.compress ⟨coins[11]!, coins[15]!⟩ ⟨coins[12]!, coins[16]!⟩
      (PE.pinRgKey q.id q.idx)))).sum =
      ((inp.prims.map fun q => (recQ (PE.pinRgKey q.id q.idx) : Fin 8 → Q)).map fun r =>
        qinv (compressQ (qmk (toKV coins[11]!) (toKV coins[15]!)) (qmk (toKV coins[12]!) (toKV coins[16]!)) r)).sum := by
    rw [List.map_map]
    refine congrArg List.sum (List.map_congr_left fun q hq => ?_)
    have hk := hP q hq
    have hkc := pinRgKey_can q.id q.idx hk.1 hk.2.2.1
    simp only [Function.comp]
    rw [(toQ6_compress _ _ _ hkc.1 hgh hrh hkc.2).2]
    rfl
  have hrgc : canon6 (inp.prims.foldl (fun s q => PE.K6.add s (PE.compress ⟨coins[11]!, coins[15]!⟩ ⟨coins[12]!, coins[16]!⟩
    (PE.pinRgKey q.id q.idx)).inv0) K6.zero) := hrg.1
  have hop := foldl_invSum (fun q : PrimRec => PE.compress ⟨coins[11]!, coins[15]!⟩ ⟨coins[12]!, coins[16]!⟩
    (PE.pinOpKey q.id q.code)) inp.prims K6.zero canon6_zero
  have hopq : (inp.prims.map fun q => qinv (toQ6 (PE.compress ⟨coins[11]!, coins[15]!⟩ ⟨coins[12]!, coins[16]!⟩
      (PE.pinOpKey q.id q.code)))).sum =
      ((inp.prims.map fun q => (recQ (PE.pinOpKey q.id q.code) : Fin 8 → Q)).map fun r =>
        qinv (compressQ (qmk (toKV coins[11]!) (toKV coins[15]!)) (qmk (toKV coins[12]!) (toKV coins[16]!)) r)).sum := by
    rw [List.map_map]
    refine congrArg List.sum (List.map_congr_left fun q hq => ?_)
    have hk := hP q hq
    have hkc := pinOpKey_can q.id q.code hk.1 hk.2.1
    simp only [Function.comp]
    rw [(toQ6_compress _ _ _ hkc.1 hgh hrh hkc.2).2]
    rfl
  have hopc : canon6 (inp.prims.foldl (fun s q => PE.K6.add s (PE.compress ⟨coins[11]!, coins[15]!⟩ ⟨coins[12]!, coins[16]!⟩
    (PE.pinOpKey q.id q.code)).inv0) K6.zero) := hop.1
  have hcl := foldl_invSum (fun r : List K6 => PE.compress ⟨coins[4]!, coins[6]!⟩ ⟨coins[5]!, coins[7]!⟩ r)
    (cr ++ pr ++ qr) K6.zero canon6_zero
  have hclq : ((cr ++ pr ++ qr).map fun r => qinv (toQ6 (PE.compress ⟨coins[4]!, coins[6]!⟩ ⟨coins[5]!, coins[7]!⟩ r))).sum =
      (((cr.map fun r => (recQ r : Fin 5 → Q)) ++ (pr.map fun r => (recQ r : Fin 5 → Q)) ++
          (qr.map fun r => (recQ r : Fin 5 → Q))).map fun r =>
        qinv (compressQ (m := 5) (qmk (toKV coins[4]!) (toKV coins[6]!)) (qmk (toKV coins[5]!) (toKV coins[7]!)) r)).sum := by
    rw [← List.map_append, ← List.map_append, List.map_map]
    refine congrArg List.sum (List.map_congr_left fun r hr => ?_)
    have hrc : r.length = 5 ∧ ∀ w ∈ r, canon6 w := by
      rcases List.mem_append.mp hr with hr | hr
      · rcases List.mem_append.mp hr with hr | hr
        · exact hcrc r hr
        · exact hprc r hr
      · exact hqrc r hr
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
    rw [toQ6_add _ _ cr3 (canon6_add _ _ (canon6_add _ _ cw0 cj2) calx), toQ6_add _ _ (canon6_add _ _ cw0 cj2) calx,
      toQ6_add _ _ cw0 cj2, tw0, tj2, talx, tch] at E
    rw [t3]; exact E
  · have E := congrArg toQ6 (beq_K6 e2)
    rw [toQ6_add _ _ cr4 caxp, taxp, tw1] at E
    rw [t4]; exact E
  · have E := congrArg toQ6 (beq_K6 e3)
    have cS1 := canon6_add _ _ crS hpinc
    have cS2 := canon6_add _ _ hrgc hopc
    have cS3 := canon6_add _ _ cS1 cS2
    have cS4 := canon6_add _ _ cS3 cj0
    have cS5 := canon6_add _ _ cS4 caxs
    rw [toQ6_add _ _ cS5 cals, toQ6_add _ _ cS4 caxs, toQ6_add _ _ cS3 cj0, toQ6_add _ _ cS1 cS2,
      toQ6_add _ _ crS hpinc, toQ6_add _ _ hrgc hopc, toQ6_add _ _ (canon6_add _ _ caMI cv1) csps, toQ6_add _ _ caMI cv1,
      taMI, tv1, tj0, taxs, tsps, tals, hpin.2, hpinq, hrg.2, hrgq, hop.2, hopq, toQ6_zero, zero_add, zero_add, zero_add] at E
    rw [tS]; exact E
  · have E := congrArg toQ6 (beq_K6 e4)
    rw [toQ6_add _ _ calv hcl.1, toQ6_add _ _ cc0 caMB, tc0, taMB, hcl.2, hclq, toQ6_zero, zero_add,
      talv] at E
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

/-- the verifier-side public relation of the J-9 AL objects (twin of `PubJ9P`): nine slices, the primitive records -/
def PubJ9LP (inp : PE.PubIn) (L : PE.PubLayout) (slotOf : Array Nat) (slots : Array VF.K3) (pub : Array UInt64) : Prop :=
  (∃ cr pr qr : List (List PE.K6),
      inp.claimCells.mapM (claimRecS ⟨(coinsOf slots slotOf)[2]!, (coinsOf slots slotOf)[3]!⟩
        ⟨(coinsOf slots slotOf)[17]!, (coinsOf slots slotOf)[18]!⟩ (slOf L pub 0)) = some cr ∧
      inp.pins.mapM (pinRecS ⟨(coinsOf slots slotOf)[2]!, (coinsOf slots slotOf)[3]!⟩
        ⟨(coinsOf slots slotOf)[17]!, (coinsOf slots slotOf)[18]!⟩) = some pr ∧
      inp.prims.mapM (primRecS ⟨(coinsOf slots slotOf)[2]!, (coinsOf slots slotOf)[3]!⟩
        ⟨(coinsOf slots slotOf)[17]!, (coinsOf slots slotOf)[18]!⟩) = some qr ∧
      PubJ9LRel (fun i : Fin 19 => toKV (coinsOf slots slotOf)[(i : ℕ)]!) (rhoOf (slOf L pub 0))
        (rhoSOf (slOf L pub 0)) (pubK (slOf L pub 1)) (pubK (slOf L pub 2)) (pubK (slOf L pub 3))
        (pubK (slOf L pub 4)) (pubK (slOf L pub 5)) (pubK (slOf L pub 6)) (pubK (slOf L pub 7)) (pubK (slOf L pub 8))
        (inp.pins.map fun q => (recQ (PE.pinConsKey q.key q.idx) : Fin 8 → Q))
        (inp.prims.map fun q => (recQ (PE.pinRgKey q.id q.idx) : Fin 8 → Q))
        (inp.prims.map fun q => (recQ (PE.pinOpKey q.id q.code) : Fin 8 → Q))
        (cr.map fun r => (recQ r : Fin 5 → Q)) (pr.map fun r => (recQ r : Fin 5 → Q))
        (qr.map fun r => (recQ r : Fin 5 → Q))) ∧
  ComputeDerivedP inp (coinsOf slots slotOf) (slOf L pub 0)

/-- **`pubCheck9L_sound`**: a true nine-table check gives `PubJ9LP` (canonical slots / publics / instance data) -/
theorem pubCheck9L_sound (inp : PE.PubIn) (L : PE.PubLayout) (slotOf : Array Nat) (slots : Array VF.K3)
    (pub : Array UInt64) (hs : ∀ s ∈ slots, canon3 s) (hp : ∀ g ∈ pub, canon g) (hinp : InpCan inp) (hP : PrimsCan inp)
    (h : PE.pubCheck9L inp L slotOf slots pub = true) : PubJ9LP inp L slotOf slots pub := by
  have h1 := (PE.pubCheckG_sound 9 PE.tabLens9L PE.chk9L (fun inp co ps => PE.chk9L inp co ps = true) (fun _ _ _ h => h)
    inp L slotOf slots pub h).2
  have e : ((List.range 9).toArray.map (PE.sliceG L pub)) =
      #[slOf L pub 0, slOf L pub 1, slOf L pub 2, slOf L pub 3, slOf L pub 4, slOf L pub 5, slOf L pub 6, slOf L pub 7,
        slOf L pub 8] := by
    simp [List.range_succ]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  rw [e] at h1
  have hc : ∀ i : ℕ, canon3 (coinsOf slots slotOf)[i]! := by
    refine canon_getBang canon3 canon3_default _ ?_
    intro g hg
    unfold coinsOf at hg
    rw [Array.mem_map] at hg
    obtain ⟨i, _, rfl⟩ := hg
    exact canon_getBang canon3 canon3_default slots hs _
  exact checkPubEq9L_sound inp (coinsOf slots slotOf)
    ⟨slOf L pub 0, slOf L pub 1, slOf L pub 2, slOf L pub 3, slOf L pub 4, slOf L pub 5, slOf L pub 6, slOf L pub 7⟩
    (slOf L pub 8) hc
    (slOf_can L pub hp 0) (slOf_can L pub hp 1) (slOf_can L pub hp 2) (slOf_can L pub hp 3) (slOf_can L pub hp 4)
    (slOf_can L pub hp 5) (slOf_can L pub hp 6) (slOf_can L pub hp 7) (slOf_can L pub hp 8) hinp hP h1

/-! ## 2. The record lemmas and `hRVU_J9AL` -/

open Polynomial
open NockvmE2E.Exec.VL
open NockvmE2E.J8.RVUJ8
open Nock.NockVMROM.Thm54.T0Tower (Quad)
open Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.ClaimJ9 (claimBigs claimBigRecs claimRecsJ9 pubVJ9 labelJ9 seedJ9 claimHJ9 claimKH isBigN)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8P (rkC claimCells pinRecsJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.FrameVS (claimNoun isCellN)
open NockvmE2E.J9A.InstJ9A (Datum9A StmtP9A PubP9A Msg9)
open NockvmE2E.J9AL.InstJ9AL (Datum9AL StmtP9AL PubP9AL PubEq9AL Mof9L)
open Nock.NockVMROM.Thm54.VclL.Handle.RealIOJ9AL (PubJ9AL)
open NockvmE2E.J8.InstJ8 (P Φ0 KQ')
open Nock.TraceGenExe (deltaF)
open Nock.Jet.Prim (PrimOp primC)
open Nock.NockVMROM.Thm54.VclL.Handle.RealIOJ9AL (primCode)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8P (pinRecsJ8)

attribute [local instance] Nock.NockVMROM.Thm54.VclL.Handle.E2EJ8Iface.twinFact Nock.NockVMROM.Thm54.VclL.Handle.E2EJ8Iface.twinAlg

theorem add_assoc_aux {G : Type*} [AddCommGroup G] (r c rg op j x l : G) :
    r + c + rg + op + j + x + l = r + c + (rg + op) + j + x + l := by abel

/-- **the datum link at J-9 AL**: J-9 A's, and the verifier's primitive table is the datum's `prims` -/
structure InpLink9L (d : Datum9AL) (inp : PE.PubIn) : Prop where
  toA : InpLink9 d.toA inp
  hprim : inp.prims = d.Pb.prims.map fun q => (⟨q.1, primCode q.2, d.Pb.idxP q.1, (d.Pb.rkP q.1).1, (d.Pb.rkP q.1).2⟩ : PE.PrimRec)

/-- a successful `mapM primRecS` over the datum's primitives: no `dec`, and the records are the claim vectors of `primC op` -/
theorem primsM (z y : PE.K6) (idxP : ℕ → ℕ) (rk : ℕ → ℕ × ℕ) :
    ∀ (l : List (ℕ × PrimOp)) (r : List (List PE.K6)),
      (l.map fun q => (⟨q.1, primCode q.2, idxP q.1, (rk q.1).1, (rk q.1).2⟩ : PE.PrimRec)).mapM (primRecS z y) = some r →
      (∀ q ∈ l, q.2 ≠ PrimOp.dec) ∧
        r = l.map fun q => PE.claimVec (fpOf z z.inv0 y (primC q.2)) (idxP q.1) (rk q.1).1 (rk q.1).2
  | [], r, h => by
      simp only [List.map_nil, List.mapM_nil, pure, Option.some.injEq] at h
      subst h; simp
  | q :: l, r, h => by
      rw [List.map_cons] at h
      obtain ⟨b, rs, hb, hrs, rfl⟩ := mapM_cons_some _ _ _ _ h
      have hq : q.2 ≠ PrimOp.dec := by
        intro hd
        have h0 : PE.primToks (primCode q.2) = none := by rw [hd]; exact NockvmE2E.Exec.PrimToksTie.primToks_dec
        unfold primRecS at hb
        simp [h0] at hb
      have ht := NockvmE2E.Exec.PrimToksTie.primToks_primCode q.2 hq
      have hb' : b = PE.claimVec (fpOf z z.inv0 y (primC q.2)) (idxP q.1) (rk q.1).1 (rk q.1).2 := by
        unfold primRecS at hb
        simp only [ht, enc_toks, bind, Option.bind, pure, Option.some.injEq] at hb
        exact hb.symm
      obtain ⟨h1, h2⟩ := primsM z y idxP rk l rs hrs
      refine ⟨fun q' hq' => ?_, ?_⟩
      · rcases List.mem_cons.1 hq' with rfl | hq'
        · exact hq
        · exact h1 q' hq'
      · rw [List.map_cons, hb', h2]

/-- the ALU keyRg pin vector against the executable one -/
theorem pinRg_spec (id idx : ℕ) (hid : id < 18446744073709551616) (hidx : idx < 18446744073709551616) :
    (fun c : Fin 8 => ψ ((PE.pinRgKey id idx).getD c PE.K6.zero)) =
      Nock.NockVMROM.Thm54.VclL.Handle.BalanceQ.liftRec (L := KQ')
        (Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ9AL.pinRgVec (p := P) (K := KN) id idx) := by
  have h1 : ∀ v : ℕ, v < 18446744073709551616 → ψ (PE.K6.base (UInt64.ofNat v)) = algebraMap KN KQ' (algebraMap (ZMod P) KN (v : ZMod P)) := by
    intro v hv
    rw [ψ_base, zv_ofNat _ hv, emb_eq]
  unfold Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ9AL.pinRgVec
  funext c
  fin_cases c
  · exact h1 id hid
  · exact h1 1 (by norm_num)
  · exact h1 idx hidx
  · exact h1 0 (by norm_num)
  · exact h1 0 (by norm_num)
  · exact h1 0 (by norm_num)
  · exact h1 0 (by norm_num)
  · exact h1 7 (by norm_num)

theorem primCode_lt (op : PrimOp) : primCode op < 18446744073709551616 := by
  cases op <;> simp [primCode]

theorem pinOp_spec (id code : ℕ) (hid : id < 18446744073709551616) (hcode : code < 18446744073709551616) :
    (fun c : Fin 8 => ψ ((PE.pinOpKey id code).getD c PE.K6.zero)) =
      Nock.NockVMROM.Thm54.VclL.Handle.BalanceQ.liftRec (L := KQ')
        (Nock.Jet.RapJetJ8.keyK (K := KN) 8
          [(id : ZMod P), (code : ZMod P), 0, 0, 0, 0, 0, ((Nock.NockVMROM.Thm54.VclL.Handle.AluSZChipJ9.tagOp : ℕ) : ZMod P)]) := by
  have h1 : ∀ v : ℕ, v < 18446744073709551616 → ψ (PE.K6.base (UInt64.ofNat v)) = algebraMap KN KQ' (algebraMap (ZMod P) KN (v : ZMod P)) := by
    intro v hv
    rw [ψ_base, zv_ofNat _ hv, emb_eq]
  funext c
  fin_cases c
  · exact h1 id hid
  · exact h1 code hcode
  · exact h1 0 (by norm_num)
  · exact h1 0 (by norm_num)
  · exact h1 0 (by norm_num)
  · exact h1 0 (by norm_num)
  · exact h1 0 (by norm_num)
  · exact h1 6 (by norm_num)

theorem pinRgR_eq9L (Pb : PubJ9AL P) (h : ∀ q ∈ Pb.prims, q.1 < 18446744073709551616 ∧ Pb.idxP q.1 < 18446744073709551616) :
    ((Pb.prims.map fun q => (SP.recQ (PE.pinRgKey q.1 (Pb.idxP q.1)) : Fin 8 → SP.Q)).map fun r c => φ (r c)) =
      (Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ9AL.pinRgP (p := P) (K := KN) Pb).map
        fun r => Nock.NockVMROM.Thm54.VclL.Handle.BalanceQ.liftRec (L := KQ') r := by
  unfold Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ9AL.pinRgP
  simp only [List.map_map]
  refine List.map_congr_left fun q hq => ?_
  exact pinRg_spec q.1 (Pb.idxP q.1) (h q hq).1 (h q hq).2

theorem pinOpR_eq9L (Pb : PubJ9AL P) (h : ∀ q ∈ Pb.prims, q.1 < 18446744073709551616) :
    ((Pb.prims.map fun q => (SP.recQ (PE.pinOpKey q.1 (primCode q.2)) : Fin 8 → SP.Q)).map fun r c => φ (r c)) =
      (Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ9AL.pinOpP (p := P) (K := KN) Pb).map
        fun r => Nock.NockVMROM.Thm54.VclL.Handle.BalanceQ.liftRec (L := KQ') r := by
  unfold Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ9AL.pinOpP
  simp only [List.map_map]
  refine List.map_congr_left fun q hq => ?_
  exact pinOp_spec q.1 (primCode q.2) (h q hq) (primCode_lt q.2)

theorem primRecs_eq9L (Pb : PubJ9AL P)
    (hlt : ∀ q ∈ Pb.prims, (Pb.rkP q.1).1 < ringChar (ZMod P) ∧ (Pb.rkP q.1).2 < ringChar (ZMod P) ∧
      Pb.idxP q.1 < ringChar (ZMod P)) (z y : PE.K6) (hz : SP.canon6 z) (hy : SP.canon6 y)
    (χ : Nock.NockVMROM.Thm54.SVFrame.Coins FrameJ8.frameJ8 KN)
    (hzψ : ψ z = Quad.mk δK (χ Nock.NockVMROM.Thm54.VclL.Handle.WeightsJ8.c2) (χ Nock.NockVMROM.Thm54.VclL.Handle.WeightsJ8.c3))
    (hyψ : ψ y = Quad.mk δK (χ FrameJ8.cY1) (χ FrameJ8.cY2)) :
    (Pb.prims.map fun q => PE.claimVec (fpOf z z.inv0 y (primC q.2)) (Pb.idxP q.1) (Pb.rkP q.1).1 (Pb.rkP q.1).2).map
        (fun r => fun c : Fin 5 => φ (SP.recQ r c)) =
      Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ9AL.pinRecsP (K := KN) deltaF Pb χ := by
  unfold Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ9AL.pinRecsP
  rw [List.map_map]
  refine List.map_congr_left fun q hq => ?_
  have hl := hlt q hq
  rw [ringChar_P] at hl
  have hi : Pb.idxP q.1 < 18446744073709551616 := lt_trans hl.2.2 P_lt
  have hh : (Pb.rkP q.1).1 < 18446744073709551616 := lt_trans hl.1 P_lt
  have hlo : (Pb.rkP q.1).2 < 18446744073709551616 := lt_trans hl.2.1 P_lt
  have e1 := claimVec_spec (fpOf z z.inv0 y (primC q.2)) (Pb.idxP q.1) _ _ hi hh hlo
  have e2 := encZY_spec z y hz hy (primC q.2)
  rw [hzψ, hyψ] at e2
  show (fun c : Fin 5 => ψ ((PE.claimVec _ _ _ _).getD c PE.K6.zero)) = _
  rw [e1, e2]

set_option maxHeartbeats 1600000 in
theorem pubEq9L_of_P (d : Datum9AL) (hS : StmtP9AL d) (inp : PE.PubIn) (hlink : InpLink9L d inp) (L : PE.PubLayout)
    (slotOf : Array ℕ) (slots : Array VF.K3) (pub : Array UInt64) (hs : ∀ s ∈ slots, canon3 s) (hp : ∀ g ∈ pub, canon g)
    (hids : ∀ id ∈ d.toA.Pb.regs, id < P)
    (χ : Nock.NockVMROM.Thm54.SVFrame.Coins FrameJ8.frameJ8 KN) (hχ : ∀ i : Fin 19, χ i = toKV (SP.coinsOf slots slotOf)[i.val]!)
    (hP : PubJ9LP inp L slotOf slots pub) :
    PubEq9AL d χ (Mof9L L pub) := by
  obtain ⟨cr, pr, qr, hcr, hpr, hqr, hrel⟩ := hP.1
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
  rw [hlink.toA.hcl] at hcr
  have hcells : ∀ k ∈ claimCells d.toA.c, isCellN (claimNoun d.toA.c k) = true := fun k hk => by
    unfold claimCells at hk; exact (List.mem_filter.1 hk).2
  have hbigs : ∀ k ∈ claimBigs P d.toA.c, isBigN P (claimNoun d.toA.c k) = true := fun k hk => by
    unfold claimBigs at hk; exact (List.mem_filter.1 hk).2
  obtain ⟨ra, rb, hra, hrb, hcr_eq⟩ := mapM_append_some _ _ _ _ hcr
  obtain ⟨-, hra'⟩ := claims_mapM _ _ (SP.slOf L pub 0) (claimNoun d.toA.c) (claimCells d.toA.c) hcells ra hra
  obtain ⟨-, hrb'⟩ := claims_mapM_big _ _ (SP.slOf L pub 0) (claimNoun d.toA.c) (claimBigs P d.toA.c) hbigs rb hrb
  rw [hlink.hprim] at hqr
  obtain ⟨hne, hqr''⟩ := primsM _ _ d.Pb.idxP d.Pb.rkP d.Pb.prims qr hqr
  have hbP : ∀ q ∈ d.Pb.prims, q.1 < 18446744073709551616 ∧ d.Pb.idxP q.1 < 18446744073709551616 := fun q hq =>
    ⟨lt_trans (hS.hlenL.2.2 q hq).1 P_lt, lt_trans (hS.hlenL.2.2 q hq).2 P_lt⟩
  have hpm := pins_mapM ⟨(SP.coinsOf slots slotOf)[2]!, (SP.coinsOf slots slotOf)[3]!⟩
    ⟨(SP.coinsOf slots slotOf)[17]!, (SP.coinsOf slots slotOf)[18]!⟩ (fun id => Nock.Jet.Autogen.compile P (d.toA.Pb.Rt id))
    d.toA.Pb.idx (fun id => (d.toA.Pb.rk id).1) (fun id => (d.toA.Pb.rk id).2) d.toA.Pb.regs
  rw [hlink.toA.hpin] at hpr
  have hpr'' := Option.some.inj (hpr.symm.trans hpm)
  have hb : ∀ id ∈ d.toA.Pb.regs, id < 18446744073709551616 ∧ d.toA.Pb.idx id < 18446744073709551616 := fun id hid =>
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
    simp only [map_add, φ_mk] at e
    exact e
  · have e := congrArg φ h2
    rw [map_add, φ_mk, φ_mk] at e
    exact e
  · have hpc : (inp.pins.map fun q => (SP.recQ (PE.pinConsKey q.key q.idx) : Fin 8 → SP.Q)) =
        d.Pb.regs.map fun id => SP.recQ (PE.pinConsKey id (d.Pb.idx id)) := by
      rw [hlink.toA.hpin, List.map_map]; rfl
    have hb3 : ∀ id ∈ d.Pb.regs, id < 18446744073709551616 ∧ d.Pb.idx id < 18446744073709551616 := hb
    have hprg : (inp.prims.map fun q => (SP.recQ (PE.pinRgKey q.id q.idx) : Fin 8 → SP.Q)) =
        d.Pb.prims.map fun q => SP.recQ (PE.pinRgKey q.1 (d.Pb.idxP q.1)) := by
      rw [hlink.hprim, List.map_map]; rfl
    have hpop : (inp.prims.map fun q => (SP.recQ (PE.pinOpKey q.id q.code) : Fin 8 → SP.Q)) =
        d.Pb.prims.map fun q => SP.recQ (PE.pinOpKey q.1 (primCode q.2)) := by
      rw [hlink.hprim, List.map_map]; rfl
    rw [hpc, hprg, hpop] at h3
    have e := congrArg φ h3
    simp only [map_add, φ_mk] at e
    rw [inv_comp, inv_comp, inv_comp, pinConsR_eq _ _ hb3, pinRgR_eq9L _ hbP, pinOpR_eq9L _ (fun q hq => (hbP q hq).1)] at e
    simp only [List.map_map, Function.comp_def] at e
    rw [VerJ8.coinsCV_J8, hg, hr]
    refine (add_assoc_aux _ _ _ _ _ _ _).trans ?_
    exact e
  · have e4 : χ Nock.NockVMROM.Thm54.VclL.Handle.WeightsJ8.c4 = toKV (SP.coinsOf slots slotOf)[4]! := hχ ⟨4, (by norm_num : 4 < 19)⟩
    have e5 : χ Nock.NockVMROM.Thm54.VclL.Handle.WeightsJ8.c5 = toKV (SP.coinsOf slots slotOf)[5]! := hχ ⟨5, (by norm_num : 5 < 19)⟩
    have e6 : χ Nock.NockVMROM.Thm54.VclL.Handle.WeightsJ8.c6 = toKV (SP.coinsOf slots slotOf)[6]! := hχ ⟨6, (by norm_num : 6 < 19)⟩
    have e7 : χ Nock.NockVMROM.Thm54.VclL.Handle.WeightsJ8.c7 = toKV (SP.coinsOf slots slotOf)[7]! := hχ ⟨7, (by norm_num : 7 < 19)⟩
    have hmap : ∀ (l : List (List PE.K6)), (l.map fun r => (SP.recQ r : Fin 5 → SP.Q)).map (fun r c => φ (r c)) =
        l.map (fun r => fun c : Fin 5 => φ (SP.recQ r c)) := by
      intro l; rw [List.map_map]; rfl
    have e := congrArg φ h4
    simp only [map_add, φ_mk] at e
    rw [inv_comp] at e
    simp only [List.map_append] at e
    rw [hmap, hmap, hmap, hcr_eq, hpr'', hqr''] at e
    simp only [List.map_append] at e
    rw [hra', hrb'] at e
    rw [claimCellRecs_eq9 d.toA hS.hclR _ _ hz hy χ hzψ hyψ _ hx, claimBigRecs_eq9 d.toA _ _ hz hy χ hzψ hyψ _ hx,
      pinRecs9_eq d.toA hS.hlt _ _ hz hy χ hzψ hyψ, primRecs_eq9L d.Pb hS.hltP _ _ hz hy χ hzψ hyψ] at e
    rw [e4, e5, e6, e7]
    unfold claimRecsJ9
    simp only [List.map_append]
    first | exact e | simpa only [add_assoc] using e | linear_combination e
  · have e := congrArg φ h5
    rw [map_add, φ_mk, φ_mk, φ_mk] at e
    exact e

/-! ### `hRVU_J9AL` -/

set_option maxHeartbeats 800000 in
/-- **`hRVU_J9A`: the public twin at J-9 A.**  The verifier-side relation `PubJ9P` gives nock's `PubP9A d χ` at the message
`Mof9 L pub`.  Hypotheses as `hRVU_J8` (`StmtP9A`, the datum link `InpLink9`, canonical slots / publics, registry ids `< p`, the coins
are the slot coins) and, for each optional table (jet, atom walk, axis, split), that an absent one has `present = false`. -/
theorem hRVU_J9AL (d : Datum9AL) (hS : StmtP9AL d) (inp : PE.PubIn) (hlink : InpLink9L d inp) (L : PE.PubLayout)
    (slotOf : Array ℕ) (slots : Array VF.K3) (pub : Array UInt64) (hs : ∀ s ∈ slots, canon3 s) (hp : ∀ g ∈ pub, canon g)
    (hids : ∀ id ∈ d.Pb.regs, id < P)
    (hpJ : d.Pb.nJ = 0 → L.present[3]! = false) (hpV : d.Pb.krootsV = 0 → L.present[5]! = false)
    (hpX : d.Pb.axOn = false → L.present[6]! = false) (hpS : d.Pb.spOn = false → L.present[7]! = false)
    (hpL : d.Pb.aluOn = false → L.present[8]! = false)
    (χ : NockvmE2E.Rap.Coins Φ0 KN) (hχ : ∀ i : Fin 19, χ i = toKV (SP.coinsOf slots slotOf)[i.val]!)
    (hP : PubJ9LP inp L slotOf slots pub) :
    PubP9AL d χ (Mof9L L pub) := by
  have hP' := hP
  obtain ⟨⟨cr, pr, qr, hcr, hpr, hqr, hrel⟩, hder⟩ := hP
  have hx : SP.ArrCan (SP.slOf L pub 0) := SP.slOf_can L pub hp 0
  have hcells : ∀ k ∈ claimCells d.toA.c, isCellN (claimNoun d.toA.c k) = true := fun k hk => by
    unfold claimCells at hk; exact (List.mem_filter.1 hk).2
  have hbigs : ∀ k ∈ claimBigs P d.toA.c, isBigN P (claimNoun d.toA.c k) = true := fun k hk => by
    unfold claimBigs at hk; exact (List.mem_filter.1 hk).2
  rw [hlink.toA.hcl] at hcr
  obtain ⟨ra, rb, hra, hrb, -⟩ := mapM_append_some _ _ _ _ hcr
  obtain ⟨hcl0, -⟩ := claims_mapM _ _ (SP.slOf L pub 0) (claimNoun d.toA.c) (claimCells d.toA.c) hcells ra hra
  obtain ⟨hbg0, -⟩ := claims_mapM_big _ _ (SP.slOf L pub 0) (claimNoun d.toA.c) (claimBigs P d.toA.c) hbigs rb hrb
  have hcl : ∀ k : Fin 3, isCellN (claimNoun d.toA.c k) = true → SP.labelOf (SP.slOf L pub 0) (2 * k.val) = 1 := by
    intro k hk
    exact hcl0 k (by unfold claimCells; exact List.mem_filter.2 ⟨List.mem_finRange k, hk⟩)
  have hbg : ∀ k : Fin 3, isBigN P (claimNoun d.toA.c k) = true → SP.labelOf (SP.slOf L pub 0) (2 * k.val) = 2 := by
    intro k hk
    exact hbg0 k (by unfold claimBigs; exact List.mem_filter.2 ⟨List.mem_finRange k, hk⟩)
  have hat : ∀ k : Fin 3, ∀ v, claimNoun d.toA.c k = .atom v → v < P →
      (SP.slOf L pub 0)[2 * k.val]! = 0 ∧ (SP.slOf L pub 0)[2 * k.val + 1]! = UInt64.ofNat v := by
    intro k v hk hv
    have hmem : (k.val, v) ∈ inp.atoms := by
      rw [hlink.toA.hat]
      exact List.mem_filterMap.2 ⟨k, List.mem_finRange k, by simp [hk, not_le.2 hv]⟩
    exact (hder.2.2.2.2.2.2 _ hmem).2
  refine ⟨pubEq9L_of_P d hS inp hlink L slotOf slots pub hs hp hids χ hχ hP', ?_, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
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
  · intro hL
    have : SP.slOf L pub 8 = Array.replicate L.lens[8]! 0 := by
      unfold SP.slOf; rw [if_neg (by simp [hpL hL])]
    show SP.pubK (SP.slOf L pub 8) 0 = 0 ∧ SP.pubK (SP.slOf L pub 8) (0 + 1) = 0 ∧ SP.pubK (SP.slOf L pub 8) 2 = 0 ∧
      SP.pubK (SP.slOf L pub 8) (2 + 1) = 0 ∧ SP.pubK (SP.slOf L pub 8) 4 = 0 ∧ SP.pubK (SP.slOf L pub 8) (4 + 1) = 0
    rw [this]
    exact ⟨pubK_replicate _ _, pubK_replicate _ _, pubK_replicate _ _, pubK_replicate _ _, pubK_replicate _ _,
      pubK_replicate _ _⟩
  · exact derived9_of d.toA inp _ hx _ hder hat hcl hbg χ (hχ ⟨13, (by norm_num : 13 < 19)⟩) (hχ ⟨14, (by norm_num : 14 < 19)⟩)

end NockvmE2E.J9AL.RVUJ9AL

#print axioms NockvmE2E.J9AL.RVUJ9AL.checkPubEq9L_sound
#print axioms NockvmE2E.J9AL.RVUJ9AL.pubCheck9L_sound
#print axioms NockvmE2E.J9AL.RVUJ9AL.primsM
#print axioms NockvmE2E.J9AL.RVUJ9AL.primRecs_eq9L
#print axioms NockvmE2E.J9AL.RVUJ9AL.pubEq9L_of_P
#print axioms NockvmE2E.J9AL.RVUJ9AL.hRVU_J9AL
