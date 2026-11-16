/-
  Nock/NockVMROM/Thm54/VclL/Handle/ServedPVS.lean

  Additive.

  * `comp_p_of_served`: a compute walk record `[root, ax, ck, cv]` whose key is among the walk twin's
    provided handle records is row `j`'s side-`bb` record: `root = ridx_j`, `ax = 2·pre_j + bb`,
    child = `childHOf bb`;
  * `GenuineWalk` — the conclusion of `WalkH.walkH_records_genuine` stated per twin row (`wEF`);
  * `genuineWalk_of_records`: `walkH_records_genuine`'s conclusion IS `GenuineWalk` of the twin rows;
  * `pkey_mem`, `idx_lt_of_den`;
  * `pok_of_genuine`: under `GenuineWalk` (and the table length below `p`), a served compute walk record
    is `POK` for `denH`;
  * **`pok_VS`**: at VS, outside the handle IO summands, every walk record a compute row consumes is
    `POK` for `denVS`, given `GenuineWalk` of the walk twin on the decoded table.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.ServedVS
import Nock.NockVMROM.Thm54.VclL.Chips.MemSoundnessVCLW

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Nock.NockVMROM.Thm54.VclL.Handle.ServedPVS

open Nock Nock.Reified Nock.Framework
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.T0Tower Module
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.TeleH Nock.NockVMROM.Thm54.VclL.Handle.ServeH
open Nock.NockVMROM.Thm54.VclL.Handle.TeleC Nock.NockVMROM.Thm54.VclL.Handle.RowDecodeVS
open Nock.NockVMROM.Thm54.VclL.Handle.LocalVS Nock.NockVMROM.Thm54.VclL.Handle.ServedVS
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.SVFrame Nock.NockVMROM.Thm54.SVFrameG
open Nock.NockVMROM.Thm54.VclL.Handle.FrameVS Nock.NockVMROM.Thm54.VclL.Handle.IOVS
open Nock.NockVMROM.Thm54.VclL.Handle.ClaimDenVS
open scoped Polynomial

noncomputable section

section Match
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq F]
  (b : Basis (Fin 3) F K) {h n : ℕ} (nodes : Fin n → F) (orbit : StrictOrbitDomain F 3 h)
  (chals pubs : ℕ → K) {w : ℕ} (Q : Fin w → F[X])

theorem entKey4_eq (eF : Env F) (r0 a0 k0 v0 : ℕ) (c : Fin 5) :
    (entKey [r0, a0, k0, v0] eF : Fin 5 → K) c =
      algebraMap F K ([eF.trace r0, eF.trace a0, eF.trace k0, eF.trace v0, 0].getD c 0) := by
  fin_cases c <;> simp [entKey, entKeyN]

/-- **A served compute walk record is a walk-twin row's side record.** -/
theorem comp_p_of_served (eF : Env F) (r0 a0 k0 v0 : ℕ)
    (hmem : (entKey [r0, a0, k0, v0] eF : Fin 5 → K) ∈
      (walkPProvs (K := K) b nodes orbit chals pubs Q).map Prod.fst) :
    ∃ (j : Fin n) (bb : Bool), eF.trace r0 = (wEF b nodes orbit chals pubs Q j).trace WChip.ridx ∧
      eF.trace a0 = 2 * (wEF b nodes orbit chals pubs Q j).trace WChip.pre + (if bb then 1 else 0) ∧
      hdc eF k0 v0 = childHOf (wEF b nodes orbit chals pubs Q j) bb := by
  obtain ⟨q, hq, hqk⟩ := List.mem_map.mp hmem
  obtain ⟨j, -, hj⟩ := List.mem_flatMap.mp hq
  have hent : ∀ (l : List (CoeffExpr F)), q.1 = keyVec5 l (wEF b nodes orbit chals pubs Q j) →
      ∀ c : Fin 5, (l.getD c (.const 0)).eval (wEF b nodes orbit chals pubs Q j) =
        [eF.trace r0, eF.trace a0, eF.trace k0, eF.trace v0, 0].getD c 0 := by
    intro l hl c
    have := congrFun hqk c
    rw [hl, entKey4_eq] at this
    exact (algebraMap F K).injective this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
  rcases hj with rfl | rfl
  · have e := hent WalkHC.recLH rfl
    have e0 := e ⟨0, by decide⟩; have e1 := e ⟨1, by decide⟩; have e2 := e ⟨2, by decide⟩
    have e3 := e ⟨3, by decide⟩
    simp [WalkHC.recLH, CoeffExpr.eval, cv] at e0 e1 e2 e3
    refine ⟨j, false, e0.symm, by simp [← e1], ?_⟩
    simp [hdc, childHOf, ← e2, ← e3]
  · have e := hent WalkHC.recRH rfl
    have e0 := e ⟨0, by decide⟩; have e1 := e ⟨1, by decide⟩; have e2 := e ⟨2, by decide⟩
    have e3 := e ⟨3, by decide⟩
    simp [WalkHC.recRH, CoeffExpr.eval, cv] at e0 e1 e2 e3
    refine ⟨j, true, e0.symm, by simp [← e1], ?_⟩
    simp [hdc, childHOf, ← e2, ← e3]

/-- **Genuine walk records** (the conclusion of `walkH_records_genuine`, per twin row): row `j`'s side
`bb` record names `/[2·pre + bb]` of the root serial's noun. -/
def GenuineWalk (D : VHandle → Option Noun) {m : ℕ} (eW : Fin m → Env F) : Prop :=
  ∀ (j : Fin m) (bb : Bool), ∃ (ri : ℕ) (rt nn : Noun),
    zq ((eW j).trace WChip.ridx) = (ri : ZMod (ringChar F)) ∧ D (true, ri) = some rt ∧
      D (childHOf (eW j) bb) = some nn ∧
      Noun.slot (2 * zq ((eW j).trace WChip.pre) + WalkVCL.bitZ bb).val rt = some nn

/-- **A served compute walk record is `POK`** under genuine walk records. -/
theorem pok_of_genuine (D : VHandle → Option Noun) (hF : GeneratedField.PrimeFieldElems F)
    (hp : 1 < ringChar F) (hlen : ∀ ri rt, D (true, ri) = some rt → ri < ringChar F)
    (hG : GenuineWalk D (wEF b nodes orbit chals pubs Q)) (eF : Env F) (r0 a0 k0 v0 : ℕ)
    (hmem : (entKey [r0, a0, k0, v0] eF : Fin 5 → K) ∈
      (walkPProvs (K := K) b nodes orbit chals pubs Q).map Prod.fst) :
    ∃ R C, D (true, natOf (eF.trace r0)) = some R ∧ D (hdc eF k0 v0) = some C ∧
      Noun.slot (natOf (eF.trace a0)) R = some C := by
  obtain ⟨j, bb, e0, e1, e2⟩ := comp_p_of_served b nodes orbit chals pubs Q eF r0 a0 k0 v0 hmem
  obtain ⟨ri, rt, nn, hz, hrt, hnn, hsl⟩ := hG j bb
  refine ⟨rt, nn, ?_, by rw [e2]; exact hnn, ?_⟩
  · rw [e0, natOf_of_zq hF (hlen _ _ hrt) hz]; exact hrt
  · rw [e1, natOf_axis hF hp]; exact hsl

end Match

section Keys
variable {F K : Type} [Field F] [Field K] [Algebra F K] [DecidableEq F]

/-- A consumed walk record's key is among the row's walk request keys. -/
theorem pkey_mem (eF : Env F) (r : List ℕ) (hr : r ∈ activePRecs eF) :
    (entKey r eF : Fin 5 → K) ∈ rowPReqs eF := by
  obtain ⟨S, hS, hx⟩ := List.mem_flatMap.mp hr
  refine List.mem_flatMap.mpr ⟨S, hS, ?_⟩
  rcases List.mem_append.mp hx with hx | hx
  · obtain ⟨x, hx', rfl⟩ := List.mem_map.mp hx
    exact List.mem_append_left _ (List.mem_map.mpr ⟨x, hx', rfl⟩)
  · refine List.mem_append_right _ ?_
    unfold pairRecs at hx
    unfold pairReqs
    cases hp : S.pair with
    | none => rw [hp] at hx; simp at hx
    | some t =>
      obtain ⟨fl, a, c⟩ := t
      rw [hp] at hx
      simp only at hx ⊢
      split_ifs at hx ⊢ with h1
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
        rcases hx with rfl | rfl <;> simp
      · simp at hx

/-- A table serial that denotes is below the table length. -/
theorem idx_lt_of_den {q : ℕ} (t : List (CellRowB0 q)) (ri : ℕ) (rt : Noun)
    (h : denH t (true, ri) = some rt) : ri < t.length := by
  simp only [denH, preZNounOfTable, fuelChip] at h
  rw [show 2 ^ 110 = (2 ^ 110 - 1) + 1 by norm_num, decodeB0] at h
  by_contra hc
  rw [List.getElem?_eq_none (by omega)] at h
  simp at h

end Keys

section Twin
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq F]
  (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))]
  (kroots : ℕ) (b : Basis (Fin 3) F K) {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F)
  (orbit : StrictOrbitDomain F 3 h) (chals pubs : ℕ → K)
  (Q : Fin (walkChipH δF kroots b hn nodes orbit chals pubs).rap.w → F[X])

/-- **`GenuineWalk` from `walkH_records_genuine`'s conclusion** (row `i = j + 1` of the walk data is
twin row `j`). -/
theorem genuineWalk_of_records (D : VHandle → Option Noun)
    (hR : ∀ i, 1 ≤ i → i ≤ n → ∀ bb : Bool,
      ∃ (ri : ℕ) (rt nn : Noun),
        ((walkDataOf δF kroots b hn nodes orbit chals pubs
          (restrictWalk δF kroots b hn nodes orbit chals pubs Q)).lbl i).2.ridx = (ri : ZMod (ringChar F)) ∧
        D (true, ri) = some rt ∧
        D (childHOf (walkEnvFH δF kroots b hn nodes orbit chals pubs Q (i - 1)) bb) = some nn ∧
        Noun.slot (2 * ((walkDataOf δF kroots b hn nodes orbit chals pubs
          (restrictWalk δF kroots b hn nodes orbit chals pubs Q)).lbl i).2.pre + WalkVCL.bitZ bb).val rt
          = some nn) :
    GenuineWalk D (wEF b nodes orbit chals pubs Q) := by
  intro j bb
  obtain ⟨ri, rt, nn, h1, h2, h3, h4⟩ := hR (j + 1) (by omega) (by omega) bb
  have hj : (j : ℕ) + 1 - 1 = j := by omega
  rw [hj] at h3
  have hE : walkEnvFH δF kroots b hn nodes orbit chals pubs Q j = wEF b nodes orbit chals pubs Q j := by
    simp [walkEnvFH, wEF]
  have hr : ((walkDataOf δF kroots b hn nodes orbit chals pubs
      (restrictWalk δF kroots b hn nodes orbit chals pubs Q)).lbl (j + 1)).2.ridx =
      zq ((wEF b nodes orbit chals pubs Q j).trace WChip.ridx) := by
    simp only [walkDataOf, lblRow, hj]
    rw [← hE, walkEnvFH_trace δF kroots b hn nodes orbit chals pubs Q j (by decide)]
  have hp : ((walkDataOf δF kroots b hn nodes orbit chals pubs
      (restrictWalk δF kroots b hn nodes orbit chals pubs Q)).lbl (j + 1)).2.pre =
      zq ((wEF b nodes orbit chals pubs Q j).trace WChip.pre) := by
    simp only [walkDataOf, lblRow, hj]
    rw [← hE, walkEnvFH_trace δF kroots b hn nodes orbit chals pubs Q j (by decide)]
  rw [hr] at h1
  rw [hp] at h4
  exact ⟨ri, rt, nn, h1, h2, hE ▸ h3, h4⟩

end Twin

section VS
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq F]
  [Fintype K] [DecidableEq K] [Fintype F] (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))]
  [DecidableEq (Quad (algebraMap F K δF))] (hT hP kr hC : ℕ)
  {sumC : VerifierData F K hC (shapeVS hT hP) → ClaimMsgVS → SummandsVS (F := F) (K := K) hT hP hC}
  {sumM : VerifierData F K hC (shapeVS hT hP) → Unit → SummandsVS (F := F) (K := K) hT hP hC}

attribute [local instance] ClaimDenVS.quadCharF ClaimDenVS.quadZAlg

/-- The walk twin's base environments at VS. -/
abbrev wEnvVS (V : VerifierData F K hC (shapeVS hT hP))
    (msg : MessagesG (compCoreVS δF hT hP hC sumC) (memCoreVS δF hT hP kr hC sumM)) (χ : Coins frameVS K) :
    Fin (V.memRows (tWS hT hP)) → Env F :=
  wEF V.basis (V.memNodes (tWS hT hP)) (V.orbitM (tWS hT hP)) (chalsVS δF χ)
    (pubsWH δF (msg.requests χ) (msg.msg2M χ).1 (msg.msg2M χ).2) (msg.Qm χ (tWS hT hP))

/-- **Every compute walk record is `POK` at VS**, outside the handle IO summands, given the walk twin's
genuine records (`GenuineWalk`, the output of `walkH_records_genuine`). -/
theorem pok_VS (V : VerifierData F K hC (shapeVS hT hP))
    (hV : V.Checks (fun a => reqBoundVS hT hP hC V a + internalBoundVS hT hP hC V a)
      (ringChar (Quad (algebraMap F K δF))))
    (msg : MessagesG (compCoreVS δF hT hP hC sumC) (memCoreVS δF hT hP kr hC sumM)) (χ : Coins frameVS K)
    (h : AcceptsG V msg χ)
    (hX : ¬ (ioSummandHX hT hP hC V).mem (msg.traces χ) χ)
    (hPm : ¬ (ioSummandHP hT hP hC V).mem (msg.traces χ) χ)
    (hG : GenuineWalk (denVS δF hT hP kr hC V msg χ) (wEnvVS δF hT hP kr hC V msg χ)) (i : Fin V.N) :
    ∀ r ∈ activePRecs (cEnvVS δF hT hP kr hC V msg χ i),
      POK (denVS δF hT hP kr hC V msg χ) (cEnvVS δF hT hP kr hC V msg χ i) r := by
  intro r hr r0 a0 k0 v0 hr4
  obtain ⟨hgM, -, -⟩ := cell_facts δF hT hP kr hC V msg χ h
  have hq : 2 ^ 63 < ringChar F := hgM.2.2.2.1
  have hkey : (entKey r (cEnvVS δF hT hP kr hC V msg χ i) : Fin 5 → K) ∈ cPVS δF hT hP kr hC V msg χ :=
    List.mem_flatMap.mpr ⟨i, List.mem_finRange i, pkey_mem _ r hr⟩
  have hsrv := (served_of_not_mem δF hT hP kr hC V hV msg χ h hX hPm).2 _ hkey
  rw [hr4] at hsrv
  refine pok_of_genuine V.basis (V.memNodes (tWS hT hP)) (V.orbitM (tWS hT hP)) (chalsVS δF χ)
    (pubsWH δF (msg.requests χ) (msg.msg2M χ).1 (msg.msg2M χ).2) (msg.Qm χ (tWS hT hP)) _ hgM.2.2.1
    (by omega) ?_ hG _ r0 a0 k0 v0 hsrv
  intro ri rt hrt
  have h1 := idx_lt_of_den _ ri rt hrt
  have h2 : ((tVS δF hT hP kr hC V msg χ).map (·.b0)).length = V.memRows (tCS hT hP) := by
    simp [cellTableOf]
  have h3 := hgM.2.2.2.2
  omega

end VS

end

end Nock.NockVMROM.Thm54.VclL.Handle.ServedPVS
