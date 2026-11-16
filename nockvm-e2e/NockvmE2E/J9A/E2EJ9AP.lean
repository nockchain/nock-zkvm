/-
part 5: the chip constraint counts from hop 0 (`consSize9`, `hsz9`), the slot-coin tie `hχ_F` over a family, the public-array
canonicalisation plumbing at the generic interface (`readPub_eq_G`), and `hrd9`.
-/
import NockvmE2E.J9A.HtieJ9A
import NockvmE2E.Exec.E2EJ8P2
import NockvmE2E.J9A.PubSoundJ9A

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.deprecated false

open Polynomial

namespace NockvmE2E.J9A.E2EJ9AP

open NockvmE2E.J8 NockvmE2E.J8.TieJ8 NockvmE2E.Rap NockvmE2E.Emit Nock.Emit
open NockvmE2E.Exec NockvmE2E.Exec.DagSem NockvmE2E.Exec.V NockvmE2E.Exec.VL NockvmE2E.Exec.E2ELR NockvmE2E.Exec.InstGen
open NockvmE2E.Exec.E2EGen NockvmE2E.Exec.ShapeF NockvmE2E.Exec.J9AChips NockvmE2E.Exec.E2EJ8P2
open NockvmE2E.J9A.InstJ9A NockvmE2E.J9A.TieJ9A NockvmE2E.J9A.GenJ9A
open NockvmE2E.J8.InstJ8 (P Φ0 ω0)
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHX9 (walkGatesFX9)
open NockvmE2E.J8.TieJ8G (sizes nsK tabX gbJ chalK)

/-! ## 1. constraint counts -/

section Cons
variable (d : Datum9A) (ders : Array NockvmE2E.Exec.Aux.Der) (cmeta : Array (ℕ × ℕ))

theorem consSize9 (s : Fin 8) (hnum : NumOK9 d s) (ch : NockvmE2E.Exec.Tr.Chip)
    (hop : HopZero ch (DOf9 d s) ders cmeta ch.baseCols) : ch.cons.size = (rt9 d s).nK := by
  let env0 : KEnv := ⟨fun _ => 0, fun _ => 0, fun _ => 0, fun _ => 0, 83⟩
  have hsz : (evalDagK ch env0).size = ch.cons.size := by simp [evalDagK]
  rw [← hsz]
  fin_cases s
  · have hv := evalDagK_hop ch _ _ (decL_of_decR decR_compute9) ders cmeta hop env0
    have hv2 := hv.trans (dagVals_comp9 (envE ders cmeta env0) rfl)
    have h1 := congrArg List.length hv2; rw [Array.length_toList] at h1
    rw [h1]
    show _ = (cRoute cArith9.length cEq9.length cAcc9.length (cSlot9 ++ walkGatesFX9).length).nK
    simp only [compVals9, List.length_append, List.length_map, cRoute]
  · have hv := evalDagK_hop ch _ _ (decL_of_decR NockvmE2E.Emit.decR_cellKW) ders cmeta hop env0
    rw [show Nock.Emit.cellKWSpec.gates = ((TSpec.ofTemplate Nock.Emit.cellKWTemplate).rename Nock.Emit.fM id id).gates from rfl,
      dagVals_nc Nock.Emit.cellKWTemplate rfl rfl rfl rfl Nock.Emit.fM] at hv
    have h1 := congrArg List.length hv; rw [Array.length_toList] at h1
    rw [h1, length_tplVals]; rfl
  · have hv := evalDagK_hop ch _ _ (decL_of_decR (decR_walkJ8_at9 _ (hnum.1 rfl))) ders cmeta hop env0
    rw [show (Nock.Emit.walkJ8SpecAt d.Pb.kroots).gates = ((TSpec.ofTemplate (tWalkJ8 d.Pb.kroots)).rename Nock.Emit.fM id id).gates
      from rfl, dagVals_nc (tWalkJ8 d.Pb.kroots) rfl rfl rfl rfl Nock.Emit.fM] at hv
    have h1 := congrArg List.length hv; rw [Array.length_toList] at h1
    rw [h1, length_tplVals]; rfl
  · have hv := evalDagK_hop ch _ _ (decL_of_decR NockvmE2E.Emit.decR_jet) ders cmeta hop env0
    rw [show Nock.Emit.jetSpec.gates = ((TSpec.ofTemplate Nock.Emit.jetTemplate).rename Nock.Emit.fJ id id).gates from rfl,
      dagVals_nc Nock.Emit.jetTemplate rfl rfl rfl rfl Nock.Emit.fJ] at hv
    have h1 := congrArg List.length hv; rw [Array.length_toList] at h1
    rw [h1, length_tplVals]; rfl
  · have hv := evalDagK_hop ch _ _ (decL_of_decR NockvmE2E.Emit.decR_atom) ders cmeta hop env0
    rw [show Nock.Emit.atomSpec.gates = ((TSpec.ofTemplate Nock.Emit.atomTemplate).rename Nock.Emit.fA id id).gates from rfl,
      dagVals_nc Nock.Emit.atomTemplate rfl rfl rfl rfl Nock.Emit.fA] at hv
    have h1 := congrArg List.length hv; rw [Array.length_toList] at h1
    rw [h1, length_tplVals]; rfl
  · have hv := evalDagK_hop ch _ _ (decL_of_decR (decR_walkV_at _ (hnum.2.1 rfl))) ders cmeta hop env0
    rw [show (Nock.Emit.walkAtomSpecAt d.Pb.krootsV).gates = ((TSpec.ofTemplate (tWalkV d.Pb.krootsV)).rename Nock.Emit.fM id id).gates
      from rfl, dagVals_nc (tWalkV d.Pb.krootsV) rfl rfl rfl rfl Nock.Emit.fM] at hv
    have h1 := congrArg List.length hv; rw [Array.length_toList] at h1
    rw [h1, length_tplVals]; rfl
  · have hv := evalDagK_hop ch _ _ (decL_of_decR decR_axis) ders cmeta hop env0
    rw [show (Nock.Emit.axisSpec).gates = ((TSpec.ofTemplate tAxis).rename Nock.Emit.fM id id).gates from rfl,
      dagVals_nc tAxis rfl rfl rfl rfl Nock.Emit.fM] at hv
    have h1 := congrArg List.length hv; rw [Array.length_toList] at h1
    rw [h1, length_tplVals]; rfl
  · have hk := hnum.2.2 rfl
    have hv := evalDagK_hop ch _ _ (decL_of_decR (decR_split_at _ hk)) ders cmeta hop env0
    rw [show (Nock.Emit.splitSpecAt d.Pb.nA).gates = ((TSpec.ofTemplate (tSplit d.Pb.nA)).rename Nock.Emit.fM id id).gates from rfl,
      dagVals_nc (tSplit d.Pb.nA) rfl rfl rfl rfl Nock.Emit.fM] at hv
    have h1 := congrArg List.length hv; rw [Array.length_toList] at h1
    rw [h1, length_tplVals]; rfl

end Cons

section Sizes
variable {XI : ExecInst} (hsh : shapeOkF famJ9A XI = true) (d : Datum9A) (hdk : DatumOK9A d) (L : Link9 XI d)
  (R : TabRestr (J9A d hdk)) (hT : R.T' = XI.tabs.size)
  (hσ : ∀ t : Fin R.T', R.σ t = sigma9 XI (Fin.cast hT t)) (hfree : (J9A d hdk).AccOn R.q)

theorem hsz9 (ders : Array NockvmE2E.Exec.Aux.Der) (cmeta : Array (ℕ × ℕ))
    (hnum : ∀ t : Fin XI.tabs.size, NumOK9 d (sigma9 XI t))
    (hop : ∀ t : Fin XI.tabs.size, HopZero XI.tabs[t].chip (DOf9 d (sigma9 XI t)) ders cmeta XI.tabs[t].chip.baseCols ∧
      XI.tabs[t].chip.baseCols = bcOf9 (sigma9 XI t)) :
    HSzG (InstG.ofJ9A XI hsh d hdk L R hT hσ hfree) :=
  fun t => consSize9 d ders cmeta _ (hnum t) _ (hop t).1

end Sizes

/-! ## 2. the slot-coin tie over a family -/

section Slots
open NockvmE2E.Exec.E2ELR NockvmE2E.Exec.InstGen NockvmE2E.Lift NockvmE2E.Lift.Alternating NockvmE2E.Rap
open NockvmE2E.J8.TieJ8G (chalK hslot_gen)

/-- **`hχ`** over a family (twin of `E2EJ8P2.hχ_X`) -/
theorem hχ_F {F : Fam} (XI : ExecInst) (hsh : shapeOkF F XI = true)
    (c0 : Block (extFrame Φ0 2) KC 0) (c1 : Block (extFrame Φ0 2) KC 1) (c2 : Block (extFrame Φ0 2) KC 2) (c3 : Block (extFrame Φ0 2) KC 3)
    (i : Fin Φ0.n) :
    restr 2 (chiOfBlocks c0 c1 c2 c3) i =
      toKV (SP.coinsOf (slotsAt XI (blockEnc sl0X c0) (blockEnc sl1X c1)) XI.slotOf)[i.val]! := by
  obtain ⟨hso, hnc⟩ := slotOf_of_shapeF hsh
  have hn0 : XI.nCoins[0]! = 13 := by rw [hnc]; rfl
  have hn1 : XI.nCoins[1]! = 6 := by rw [hnc]; rfl
  have hi19 : i.val < 19 := i.2
  rw [SP.coinsOf_get _ _ i.val hi19, hso]
  have hq := slot_tab i
  have hcoin := NockvmE2E.J8.InstJ8.hcoin0 i
  have hor : Φ0.sampledAfter i = 0 ∨ Φ0.sampledAfter i = 1 := by omega
  have hlt19 : J8Shape.slotOfJ8[i.val]! < 13 + 6 := by
    rcases hor with h | h
    · have := (hq.1 h); omega
    · have := (hq.2 h); omega
  have hslot := hslot_gen Φ0 XI (derived_of_shapeF hsh) hn0 hn1 sl0X sl1X c0 c1 c2 c3 J8Shape.slotOfJ8[i.val]! hlt19
  rw [hslot]
  unfold chalK
  rcases hor with h | h
  · have hlt := hq.1 h
    rw [dif_pos hlt]
    have h0 : (extFrame Φ0 2).sampledAfter (extC Φ0 2 i) = 0 := by rw [sa_ext]; exact h
    have e : sl0X.symm ⟨J8Shape.slotOfJ8[i.val]!, hlt⟩ = ⟨extC Φ0 2 i, h0⟩ :=
      (Equiv.symm_apply_eq _).2 (Fin.ext (sl0X_val i h0)).symm
    congr 1
    apply Fin.ext
    simp only [e, extC]
  · have hge := hq.2 h
    rw [dif_neg (by omega), dif_pos (by omega)]
    have h1 : (extFrame Φ0 2).sampledAfter (extC Φ0 2 i) = 1 := by rw [sa_ext]; exact h
    have e : sl1X.symm ⟨J8Shape.slotOfJ8[i.val]! - 13, by omega⟩ = ⟨extC Φ0 2 i, h1⟩ :=
      (Equiv.symm_apply_eq _).2 (Fin.ext (sl1X_val i h1)).symm
    congr 1
    apply Fin.ext
    simp only [e, extC]

end Slots

/-! ## 3. the public read at the generic interface -/

section Rd
open NockvmE2E.Exec.E2EJ8P (readPub readPub_get)
open NockvmE2E.Exec.E2EJ8P2 (canonPub canon_cf)
open NockvmE2E.Exec.E2EFinal NockvmE2E.Exec.E2EMain NockvmE2E.Exec.E2EFri

theorem readPub_eq_G {F : Fam} {J : RapAirJ (ZMod NockvmE2E.Exec.p) NockvmE2E.Exec.KC} {XI : ExecInst} (IG : InstG F J XI) (npub : ℕ)
    (tp : Fin IG.Jm.T) (hcap : IG.Cap npub) (hnpub : npub = XI.pubOf.size) (hr : (IG.JJ npub tp hcap).r = XI.r)
    (hkd : ∀ c < XI.nc, XI.colKind[c]! < 3)
    {M0 : Type} (m0 : M0) (nq : ℕ) (vT : Array (Array VF.K3)) (vQ : Array VF.K3) (hsh : VShape XI vT vQ) :
    readPub npub (fun j => (finDecG XI (cIG IG npub tp hcap hnpub) (IG.JJ npub tp hcap).r nq m0 (deepMsg vT vQ)).2.1 (Sum.inr j, 0))
      = canonPub (pubAt XI vT) := by
  rw [finDecG_vT XI (cIG IG npub tp hcap hnpub) _ nq hr hkd m0 vT vQ hsh]
  apply Array.ext
  · simp [readPub, canonPub, pubAt, hnpub]
  · intro i h1 h2
    have hi : i < npub := by simpa [readPub] using h1
    have : (readPub npub fun j => vTOfG XI (cIG IG npub tp hcap hnpub) (IG.JJ npub tp hcap).r vT (Sum.inr j, 0))[i]'h1 =
        UInt64.ofNat (HdagU.coord0 (vTOfG XI (cIG IG npub tp hcap hnpub) (IG.JJ npub tp hcap).r vT (Sum.inr ⟨i, hi⟩, 0))).val := by
      simp [readPub]
    rw [this]
    simp only [canonPub, pubAt, Array.getElem_map]
    have hp : i < XI.pubOf.size := by rw [← hnpub]; exact hi
    have e1 : ((cIG IG npub tp hcap hnpub (Sum.inr ⟨i, hi⟩) : Fin XI.nc) : ℕ) = XI.pubOf[i] := by
      show XI.pubOf[i]! = _
      exact getElem!_pos _ i hp
    have e2 : vTOfG XI (cIG IG npub tp hcap hnpub) (IG.JJ npub tp hcap).r vT (Sum.inr ⟨i, hi⟩, 0) =
        toKV ((vT[XI.pubOf[i]]!)[0]!) := by
      unfold vTOfG
      simp only [e1]
      simp
    rw [e2, HdagU.coord0_toKV, ofNat_zvval]

/-- the instance atoms are canonical (from the J-9 A datum link) -/
theorem hat9 (d : Datum9A) (inp : PE.PubIn) (hlink : NockvmE2E.J9A.RVUJ9A.InpLink9 d inp) :
    ∀ a ∈ inp.atoms, a.2 < NockvmE2E.Exec.p := by
  intro a ha
  rw [hlink.hat] at ha
  obtain ⟨k, -, hk⟩ := List.mem_filterMap.mp ha
  cases hc : Nock.NockVMROM.Thm54.VclL.Handle.FrameVS.claimNoun d.c k with
  | cell _ _ => simp [hc] at hk
  | atom v =>
    by_cases hv : P ≤ v
    · simp [hc, hv] at hk
    · simp only [hc, hv, if_false, Option.some.injEq] at hk
      subst hk
      exact not_le.mp hv

/-- **`hrd` at J-9 A**: the exec chain carries the J-9 A public relation `PubJ9P` (`pubMode = 2`, `PubSound`), so no bridge is needed -/
theorem hrd9 {XI : ExecInst} (hsh : shapeOkF famJ9A XI = true) (d : Datum9A) (hdk : DatumOK9A d) (L : Link9 XI d)
    (R : TabRestr (J9A d hdk)) (hT : R.T' = XI.tabs.size)
    (hσ : ∀ t : Fin R.T', R.σ t = sigma9 XI (Fin.cast hT t)) (hfree : (J9A d hdk).AccOn R.q)
    (npub : ℕ) (tp) (hcap) (hnpub : npub = XI.pubOf.size)
    (hlink : NockvmE2E.J9A.RVUJ9A.InpLink9 d XI.pubIn)
    {M0 : Type} (m0 : M0) (nq : ℕ) (slots : Array VF.K3) (vT : Array (Array VF.K3)) (vQ : Array VF.K3) (hv : VShape XI vT vQ)
    (hP : NockvmE2E.J9A.RVUJ9A.PubJ9P XI.pubIn XI.pubLay XI.slotOf slots (pubAt XI vT)) :
    ∃ pub : Array UInt64, (∀ g ∈ pub, canon g) ∧ NockvmE2E.J9A.RVUJ9A.PubJ9P XI.pubIn XI.pubLay XI.slotOf slots pub ∧
      (prG (InstG.ofJ9A XI hsh d hdk L R hT hσ hfree) npub tp hcap).rd
        (fun c => (finDecG XI (cIG (InstG.ofJ9A XI hsh d hdk L R hT hσ hfree) npub tp hcap hnpub)
          ((InstG.ofJ9A XI hsh d hdk L R hT hσ hfree).JJ npub tp hcap).r nq m0 (deepMsg vT vQ)).2.1 (c, 0)) =
        NockvmE2E.J9A.RVUJ9A.Mof9 XI.pubLay pub := by
  refine ⟨canonPub (pubAt XI vT), ?_, NockvmE2E.J9A.PubSoundJ9A.pubJ9P_canon _ _ _ _ _ (hat9 d _ hlink) hP, ?_⟩
  · intro g hg
    obtain ⟨a, -, rfl⟩ := Array.mem_map.mp hg
    exact canon_cf a
  · show NockvmE2E.J9A.RVUJ9A.Mof9 XI.pubLay (readPub npub (fun j => (finDecG XI (cIG (InstG.ofJ9A XI hsh d hdk L R hT hσ hfree) npub tp hcap hnpub)
      ((InstG.ofJ9A XI hsh d hdk L R hT hσ hfree).JJ npub tp hcap).r nq m0 (deepMsg vT vQ)).2.1 (Sum.inr j, 0))) = _
    rw [readPub_eq_G (InstG.ofJ9A XI hsh d hdk L R hT hσ hfree) npub tp hcap hnpub (by show (2 : ℕ) = XI.r; exact (r_of_shapeF hsh).symm)
      (hkd_F hsh) m0 nq vT vQ hv]

end Rd

end NockvmE2E.J9A.E2EJ9AP

#print axioms NockvmE2E.J9A.E2EJ9AP.consSize9
#print axioms NockvmE2E.J9A.E2EJ9AP.hsz9
#print axioms NockvmE2E.J9A.E2EJ9AP.hχ_F
#print axioms NockvmE2E.J9A.E2EJ9AP.readPub_eq_G
#print axioms NockvmE2E.J9A.E2EJ9AP.hat9
#print axioms NockvmE2E.J9A.E2EJ9AP.hrd9
