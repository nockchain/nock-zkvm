/-
  Nock/NockVMROM/Thm54/VclL/Handle/ClaimVS.lean

  Additive.

  * `claim_decode`: a verifier-computed claim record `(enc z x, lo + hi√δ, idx)` equal to the cell
    table's validity provider key of row `j` is `ValidityProvided` at the decoded table, with the serial
    and rank halves read through `natOf`.
  * `claims_served`: on the (restricted) cell chip, the validity accumulator's LogUp at `(γ′, ρ′)` with the
    EXTERNAL consumer list `claimRecs` (the verifier's own records; their reciprocal sum is the public
    `ρ₀`, checked by `GoodCVS`), outside the weighted validity IO event and under the consumer count,
    serves every claim record.
  * `claims_provided_VS`: at VS, from `AcceptsG` and `V.Checks` (budget `3 + 2T`), outside the validity
    IO event at `(χ₄ + χ₆√δ, χ₅ + χ₇√δ)`: every CELL claim noun `x` (subject / formula / result) has
    `ValidityProvided (cellTableOf …) (enc z′ x, natOf hi, natOf lo, natOf idx)`, the input of
    `claim_handles_denote` (with `idxOf x = natOf (idx : 𝔽)`, the value the compute row's public handle
    holds).
-/
import Nock.NockVMROM.Thm54.VclL.Handle.IOVS

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.NockVMROM.Thm54.VclL.Handle.ClaimVS

open Nock Nock.Reified Nock.Framework
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.SVFrame
open Module
open scoped Polynomial

noncomputable section

section Decode
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq F]
  (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))]
  (b : Basis (Fin 3) F K) {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F)
  (orbit : StrictOrbitDomain F 3 h) (chals pubs : ℕ → K)
  (Q : Fin (cellChip δF b hn nodes orbit chals pubs).rap.w → F[X])

/-- A claim-shaped validity key: fingerprint, `lo + hi√δ`, serial. -/
def claimVec (e : ComputeTable.FP (Quad (algebraMap F K δF))) (idx hi lo : F) :
    Fin 5 → Quad (algebraMap F K δF) :=
  fun c => match (c : ℕ) with
    | 0 => e.size
    | 1 => e.dyck
    | 2 => e.leaf
    | 3 => Quad.mk _ (algebraMap F K lo) (algebraMap F K hi)
    | _ => Quad.mk _ (algebraMap F K idx) 0

/-- **Decoding a served claim record** into the existence form `ValidityProvided`. -/
theorem claim_decode (e : ComputeTable.FP (Quad (algebraMap F K δF))) (idx hi lo : F) (j : Fin n)
    (hk : claimVec δF e idx hi lo = cellKey δF b hn nodes orbit chals pubs Q 5 Cell.vKeyP j) :
    ValidityProvided (cellTableOf δF b nodes orbit chals pubs Q) (e, natOf hi, natOf lo, natOf idx) := by
  have ex : ∀ c : Fin 5, _ := fun c => congrFun hk c
  have e0 := ex 0; have e1 := ex 1; have e2 := ex 2; have e3 := ex 3; have e4 := ex 4
  simp only [claimVec, cellKey, keyVec, Cell.vKeyP, QFP.var, QFP.entries, List.cons_append,
    List.nil_append, Fin.isValue, Fin.val_zero, Fin.val_one, Fin.val_two, List.getD_cons_zero,
    List.getD_cons_succ] at e0 e1 e2 e3 e4
  have e3' : (3 : Fin 5).val = 3 := rfl
  have e4' : (4 : Fin 5).val = 4 := rfl
  simp only [e3', e4', List.getD_cons_succ, List.getD_cons_zero] at e3 e4
  rw [ev_mk2, Quad.mk_eq_mk_iff] at e3
  rw [ev_base, liftQ, ← Quad.mk_base] at e4
  refine ⟨_, List.mem_ofFn.mpr ⟨j, rfl⟩, ?_⟩
  simp only [cellRowOf, cellB0Of, Prod.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_⟩
  · cases e
    simp only [QFP.ev, QFP.var] at e0 e1 e2 ⊢
    rw [e0, e1, e2]
  · rw [(algebraMap F K).injective e3.2]; rfl
  · rw [(algebraMap F K).injective e3.1]; rfl
  · rw [Quad.mk_eq_mk_iff] at e4
    rw [(algebraMap F K).injective e4.1]; rfl

/-- **The external validity consumers are served**: every record of the verifier-side list `reqs`
(whose reciprocal sum is the public `ρ₀`) is a provider key of some row. -/
theorem ext_served [DecidableEq (Quad (algebraMap F K δF))] [Fintype K]
    (hsat : (cellChip δF b hn nodes orbit chals pubs).rap.Satisfies Q)
    (hbind : (cellChip δF b hn nodes orbit chals pubs).BindsPreprocessing Q)
    (hinj : Function.Injective nodes)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω)
    (γ ρ : Quad (algebraMap F K δF)) (hok : ChalsOK δF chals γ ρ 11)
    {p : ℕ} [CharP (Quad (algebraMap F K δF)) p] (reqs : List (Fin 5 → Quad (algebraMap F K δF)))
    (hsum : (reqs.map fun r => (FiniteIO.compress (m := 5) ⟨γ, ρ⟩ r)⁻¹).sum = Quad.mk _ (pubs 0) (pubs 1))
    (hout : (γ, ρ) ∉ FiniteIO.IOFailureEventW (reqs ++ cellVInternal δF b hn nodes orbit chals pubs Q)
      (SVFrame.liftWts (cellVRecords δF b hn nodes orbit chals pubs Q)))
    (hcount : (reqs ++ cellVInternal δF b hn nodes orbit chals pubs Q).length < p) :
    ∀ r ∈ reqs, ∃ j : Fin n, cellKey δF b hn nodes orbit chals pubs Q 5 Cell.vKeyP j = r := by
  set M := cellValidityFacts δF b hn nodes orbit chals pubs Q hsat hbind hinj hadj γ ρ hok with hM
  have hne := TeleC.den_ne_of_out _ _ γ ρ hout
  rw [FiniteIO.mem_IOFailureEventW_iff] at hout
  push Not at hout
  have hlook := FiniteIO.finiteIO_lookup_sound_weighted (p := p)
    (reqs ++ cellVInternal δF b hn nodes orbit chals pubs Q) (SVFrame.liftWts M.records) ⟨γ, ρ⟩
    hne
    (by
      intro q hq
      obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hq
      exact M.ne_zero r hr)
    (by
      rw [List.map_append, List.sum_append, hsum]
      have := M.sum_eq
      simp only [SVFrame.liftWts, List.map_map, Function.comp_def]
      exact this.symm)
    hcount hout.1 hout.2.2
  intro r hr
  have := hlook r (List.mem_append_left _ hr)
  rw [SVFrame.liftWts_fst] at this
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp this
  obtain ⟨j, -, rfl⟩ := List.mem_map.mp hq
  exact ⟨j, rfl⟩

theorem cellVInternal_length_le [Fintype K] [DecidableEq (Quad (algebraMap F K δF))] :
    (cellVInternal δF b hn nodes orbit chals pubs Q).length ≤ 2 * n := by
  unfold cellVInternal
  rw [List.length_flatMap]
  calc _ ≤ ((List.finRange n).map fun _ => 2).sum := List.sum_le_sum fun i _ => by
          rw [List.length_append]
          have h1 : (if cellB δF b hn nodes orbit chals pubs Q Cell.wL i = 1 then
              [cellKey δF b hn nodes orbit chals pubs Q 5 Cell.vKeyL i] else []).length ≤ 1 := by
            split_ifs <;> simp
          have h2 : (if cellB δF b hn nodes orbit chals pubs Q Cell.wR i = 1 then
              [cellKey δF b hn nodes orbit chals pubs Q 5 Cell.vKeyR i] else []).length ≤ 1 := by
            split_ifs <;> simp
          omega
    _ = 2 * n := by simp [mul_comm]

end Decode


/-! ## At VS: every cell claim noun's record is provided -/

section VS
open FrameVS SVFrameG

variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq F]
  [Fintype K] [DecidableEq K] [Fintype F] (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))]
  [DecidableEq (Quad (algebraMap F K δF))] (hT hP kr hC : ℕ)
  {sumC : VerifierData F K hC (shapeVS hT hP) → ClaimMsgVS → SummandsVS (F := F) (K := K) hT hP hC}
  {sumM : VerifierData F K hC (shapeVS hT hP) → Unit → SummandsVS (F := F) (K := K) hT hP hC}

theorem chalsOK_VS (χ : Coins frameVS K) :
    ChalsOK δF (chalsVS δF χ) (Quad.mk _ (χ ⟨4, by decide⟩) (χ ⟨6, by decide⟩))
      (Quad.mk _ (χ ⟨5, by decide⟩) (χ ⟨7, by decide⟩)) 11 := by
  have h := chalsVCL_ok δF (toVCL χ) 11
  refine ⟨?_, fun i hi => ?_⟩
  · rw [chalsVS_old δF χ 5 (by decide), chalsVS_old δF χ 7 (by decide)]; exact h.1
  · rw [chalsVS_old δF χ _ (by omega), chalsVS_old δF χ _ (by omega)]; exact h.2 i hi

theorem claimKey_vec (χ : Coins frameVS K) (x : Noun) (r : ℕ × ℕ × ℕ) :
    claimKey δF χ x r = claimVec δF (GlobalCarryRecognizer.enc (zVS δF χ) x) (r.1 : F) (r.2.1 : F) (r.2.2 : F) := by
  funext c
  fin_cases c <;> rfl

/-- The restricted cell trace at VS (the twin's base and original roles). -/
abbrev qCellVS (V : VerifierData F K hC (shapeVS hT hP))
    (msg : MessagesG (compCoreVS δF hT hP hC sumC) (memCoreVS δF hT hP kr hC sumM)) (χ : Coins frameVS K) :=
  restrictCell δF V.basis (V.hM (tCS hT hP)) (V.memNodes (tCS hT hP)) (V.orbitM (tCS hT hP)) (chalsVS δF χ)
    (pubsCH δF (msg.requests χ) (msg.msg2M χ).1 (msg.msg2M χ).2)
    (fun j => msg.Qm χ (tCS hT hP) (Fin.cast (TeleC.cellW δF hT hP _ _ _ _ _ _) j))

/-- Under `V.Checks`, at an
accepted coin, outside the weighted validity IO event at `(γ′, ρ′) = (χ₄ + χ₆√δ, χ₅ + χ₇√δ)` with the
verifier's claim records as the external consumers: every CELL claim noun `x = s, f, e` has its
record provided by a row of the decoded cell table, `ValidityProvided (cellTableOf …)
(enc z′ x, natOf hi, natOf lo, natOf idx)` with `(idx, hi, lo)` the claim message. -/
theorem claims_provided_VS (V : VerifierData F K hC (shapeVS hT hP))
    (hV : V.Checks (fun a => reqBoundVS hT hP hC V a + internalBoundVS hT hP hC V a)
      (ringChar (Quad (algebraMap F K δF))))
    (msg : MessagesG (compCoreVS δF hT hP hC sumC) (memCoreVS δF hT hP kr hC sumM)) (χ : Coins frameVS K)
    (h : AcceptsG V msg χ)
    (hio : (Quad.mk (algebraMap F K δF) (χ ⟨4, by decide⟩) (χ ⟨6, by decide⟩),
        Quad.mk (algebraMap F K δF) (χ ⟨5, by decide⟩) (χ ⟨7, by decide⟩)) ∉
      FiniteIO.IOFailureEventW (claimRecs δF V.claim msg.msg0C χ ++
          cellVInternal δF V.basis (V.hM (tCS hT hP)) (V.memNodes (tCS hT hP)) (V.orbitM (tCS hT hP))
            (chalsVS δF χ) (pubsCH δF (msg.requests χ) (msg.msg2M χ).1 (msg.msg2M χ).2)
            (qCellVS δF hT hP kr hC V msg χ))
        (SVFrame.liftWts (cellVRecords δF V.basis (V.hM (tCS hT hP)) (V.memNodes (tCS hT hP))
          (V.orbitM (tCS hT hP)) (chalsVS δF χ) (pubsCH δF (msg.requests χ) (msg.msg2M χ).1 (msg.msg2M χ).2)
          (qCellVS δF hT hP kr hC V msg χ)))) :
    ∀ k : Fin 3, isCellN (claimNoun V.claim k) = true →
      ValidityProvided (cellTableOf δF V.basis (V.memNodes (tCS hT hP)) (V.orbitM (tCS hT hP)) (chalsVS δF χ)
          (pubsCH δF (msg.requests χ) (msg.msg2M χ).1 (msg.msg2M χ).2) (qCellVS δF hT hP kr hC V msg χ))
        (GlobalCarryRecognizer.enc (zVS δF χ) (claimNoun V.claim k), natOf ((msg.msg0C k).2.1 : F),
          natOf ((msg.msg0C k).2.2 : F), natOf ((msg.msg0C k).1 : F)) := by
  obtain ⟨hg, -⟩ := compute_facts δF hT hP kr hC V msg χ h
  obtain ⟨-, hwT, hsatT⟩ := cell_facts δF hT hP kr hC V msg χ h
  have hsatO := cellChipH_restrict_sat δF V.basis (V.hM (tCS hT hP)) (V.memNodes (tCS hT hP))
    (V.orbitM (tCS hT hP)) (chalsVS δF χ) (pubsCH δF (msg.requests χ) (msg.msg2M χ).1 (msg.msg2M χ).2)
    _ hsatT.1
  have hbindO := cellChipH_restrict_bind δF V.basis (V.hM (tCS hT hP)) (V.memNodes (tCS hT hP))
    (V.orbitM (tCS hT hP)) (chalsVS δF χ) (pubsCH δF (msg.requests χ) (msg.msg2M χ).1 (msg.msg2M χ).2)
    _ hsatT.2
  have hchar : ringChar (Quad (algebraMap F K δF)) = ringChar F := ringChar_quad_eq δF
  haveI : CharP (Quad (algebraMap F K δF)) (ringChar F) := by rw [← hchar]; exact ringChar.charP _
  have hcons0 := hV.hcons 0
  simp [reqBoundVS, internalBoundVS, hchar] at hcons0
  have hsrv := ext_served δF V.basis (V.hM (tCS hT hP)) (V.memNodes (tCS hT hP)) (V.orbitM (tCS hT hP))
    (chalsVS δF χ) (pubsCH δF (msg.requests χ) (msg.msg2M χ).1 (msg.msg2M χ).2) _ hsatO hbindO
    (hV.memNodes_injective _) (hV.hadjM _) _ _ (chalsOK_VS δF χ) (p := ringChar F)
    (claimRecs δF V.claim msg.msg0C χ) ?_ hio ?_
  · intro k hk
    have hmem : claimKey δF χ (claimNoun V.claim k) (msg.msg0C k) ∈ claimRecs δF V.claim msg.msg0C χ :=
      List.mem_map.mpr ⟨k, List.mem_filter.mpr ⟨List.mem_finRange k, hk⟩, rfl⟩
    obtain ⟨j, hj⟩ := hsrv _ hmem
    rw [claimKey_vec] at hj
    exact claim_decode δF V.basis (V.hM (tCS hT hP)) (V.memNodes (tCS hT hP)) (V.orbitM (tCS hT hP))
      (chalsVS δF χ) (pubsCH δF (msg.requests χ) (msg.msg2M χ).1 (msg.msg2M χ).2) _ _ _ _ _ j hj.symm
  · rw [show (pubsCH δF (msg.requests χ) (msg.msg2M χ).1 (msg.msg2M χ).2 0) =
        pubsC δF (rho3 δF (msg.requests χ)) (msg.msg2M χ).1 0 by simp [pubsCH, CellH.pubH],
      show (pubsCH δF (msg.requests χ) (msg.msg2M χ).1 (msg.msg2M χ).2 1) =
        pubsC δF (rho3 δF (msg.requests χ)) (msg.msg2M χ).1 1 by simp [pubsCH, CellH.pubH],
      pubsC_01]
    simp only [rho3]
    exact hg.2.2.2.1.symm
  · rw [List.length_append]
    have h1 := claimRecs_length_le δF V.claim msg.msg0C χ
    have h2 := cellVInternal_length_le δF V.basis (V.hM (tCS hT hP)) (V.memNodes (tCS hT hP))
      (V.orbitM (tCS hT hP)) (chalsVS δF χ) (pubsCH δF (msg.requests χ) (msg.msg2M χ).1 (msg.msg2M χ).2)
      (qCellVS δF hT hP kr hC V msg χ)
    exact lt_of_le_of_lt (Nat.add_le_add h1 h2) (by omega)

end VS

end

end Nock.NockVMROM.Thm54.VclL.Handle.ClaimVS
