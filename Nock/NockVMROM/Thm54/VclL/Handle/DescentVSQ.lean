/-
  Nock/NockVMROM/Thm54/VclL/Handle/DescentVSQ.lean

  Additive.

  * `listsQ_at`: at every coin, the coin-free round-0 lists of the projection at the transported datum
    (`reqX0 / provX0 / reqP0 / provP0 (toVSV V) (projQ tr)`) ARE the VSQ chips' lists `cXQ ++ wXQ`, `tXQ`,
    `cPQ`, `wPQ` (they read round-0 columns only, at every width);
  * `cXQ_len` / `cPQ_len`: the compute consumer budgets `3N` / `2N` at the `𝕂′` compute twin;
  * `den_of_not_pole`: outside the pole-hit component every lifted denominator is nonzero;
  * **`kX_identity` / `kP_identity`**: at an `AcceptsG`-accepted VSQ coin outside the two `𝕂′` handle
    summands `ioSummandHXQ / ioSummandHPQ`, for EVERY `f : (Fin 5 → 𝕂) → 𝕂`,
    `Σ_{reqX0} f = Σ_{provX0} w · f` and `Σ_{reqP0} f = Σ_{provP0} w · f` (multiset identities; in
    particular the `𝕂` LogUp identities at every pole-free `(γ, ρ) ∈ 𝕂²`), via `BalanceQ.logup_descends`.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.PathVSQ

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Nock.NockVMROM.Thm54.VclL.Handle.DescentVSQ

open Nock Nock.Reified Nock.Framework Module Polynomial
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.T0Tower Nock.NockVMROM.Thm54.FiniteIO Nock.NockVMROM.Thm54.SVFrame
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.VclL.Compute.LogUp
open Nock.NockVMROM.Thm54.VclL.Handle Nock.NockVMROM.Thm54.VclL.Handle.FrameVS
open Nock.NockVMROM.Thm54.VclL.Handle.FrameVSQ Nock.NockVMROM.Thm54.VclL.Handle.ChipH
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHQ Nock.NockVMROM.Thm54.VclL.Handle.BalanceQ
open Nock.NockVMROM.Thm54.VclL.Handle.BalanceVSQ Nock.NockVMROM.Thm54.VclL.Handle.PathVSQ
open Nock.NockVMROM.Thm54.VclL.Handle.IOVS Nock.NockVMROM.Thm54.VclL.Handle.ChoiceQ
open Nock.NockVMROM.Thm54.VclL.Handle.SummandsHQ Nock.NockVMROM.Thm54.VclL.Handle.TeleC
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler

noncomputable section

/-! ## 1. Round-0 lists across widths -/

section Widths
variable {F K : Type} [Field F] [Field K] [Algebra F K] [DecidableEq F]

/-- Trace agreement of two row environments built from column families of DIFFERENT widths agreeing
below `B`. -/
theorem envOfTrace_congrW {w w' : ℕ} (B : ℕ) (Q : Fin w → F[X]) (Q' : Fin w' → F[X]) (hB : B ≤ w)
    (hB' : B ≤ w') (hQ : ∀ (c : ℕ) (h1 : c < w) (h2 : c < w'), c < B → Q ⟨c, h1⟩ = Q' ⟨c, h2⟩)
    (ω ω' x : F) (cv pv cv' pv' : ℕ → F) :
    ∀ c < B, (Reify.envOfTrace Q ω x cv pv).trace c = (Reify.envOfTrace Q' ω' x cv' pv').trace c := by
  intro c hc
  simp only [Reify.envOfTrace, dif_pos (lt_of_lt_of_le hc hB), dif_pos (lt_of_lt_of_le hc hB')]
  rw [hQ c _ _ hc]

theorem compReqs_congrW {h n w w' : ℕ} (nodes : Fin n → F) (orbit : StrictOrbitDomain F 3 h)
    (cv pv cv' pv' : ℕ → F) (Q : Fin w → F[X]) (Q' : Fin w' → F[X]) (hB : 43 ≤ w) (hB' : 43 ≤ w')
    (hQ : ∀ (c : ℕ) (h1 : c < w) (h2 : c < w'), c < 43 → Q ⟨c, h1⟩ = Q' ⟨c, h2⟩) :
    (compXReqs nodes cv pv orbit Q : List (Fin 5 → K)) = compXReqs nodes cv' pv' orbit Q' ∧
      (compPReqs nodes cv pv orbit Q : List (Fin 5 → K)) = compPReqs nodes cv' pv' orbit Q' := by
  have hrow := fun i : Fin n => rowReqs_congr (K := K) (Reify.envOfTrace Q orbit.ω (nodes i) cv pv)
    (Reify.envOfTrace Q' orbit.ω (nodes i) cv' pv') (envOfTrace_congrW 43 Q Q' hB hB' hQ _ _ _ _ _ _ _)
  refine ⟨?_, ?_⟩
  · unfold compXReqs; simp only [List.flatMap]; congr 1
    exact List.map_congr_left fun i _ => (hrow i).1
  · unfold compPReqs; simp only [List.flatMap]; congr 1
    exact List.map_congr_left fun i _ => (hrow i).2

variable (b : Basis (Fin 3) F K) {h h' n w w' : ℕ} (nodes : Fin n → F) (orbit : StrictOrbitDomain F 3 h)
  (orbit' : StrictOrbitDomain F 3 h') (chals pubs chals' pubs' : ℕ → K) (Q : Fin w → F[X]) (Q' : Fin w' → F[X])

theorem walkLists_congrW (hB : 25 ≤ w) (hB' : 25 ≤ w')
    (hQ : ∀ (c : ℕ) (h1 : c < w) (h2 : c < w'), c < 25 → Q ⟨c, h1⟩ = Q' ⟨c, h2⟩) :
    ServeH.walkXReqs b nodes orbit chals pubs Q = ServeH.walkXReqs b nodes orbit' chals' pubs' Q' ∧
      ServeH.walkPProvs b nodes orbit chals pubs Q = ServeH.walkPProvs b nodes orbit' chals' pubs' Q' := by
  have he := fun i : Fin n => envOfTrace_congrW 25 Q Q' hB hB' hQ orbit.ω orbit'.ω (nodes i)
    (slotVal b 25 chals) (slotVal b 25 pubs) (slotVal b 25 chals') (slotVal b 25 pubs')
  refine ⟨?_, ?_⟩
  · unfold ServeH.walkXReqs
    exact List.map_congr_left fun i _ => keyVec5_congr 25 _ xKeyH_read _ _ (he i)
  · unfold ServeH.walkPProvs
    simp only [List.flatMap]
    congr 1
    refine List.map_congr_left fun i _ => ?_
    rw [keyVec5_congr 25 _ recLH_read _ _ (he i), keyVec5_congr 25 _ recRH_read _ _ (he i),
      he i WChip.mL (by decide), he i WChip.mR (by decide)]

theorem cellProvs_congrW (hB : 130 ≤ w) (hB' : 130 ≤ w')
    (hQ : ∀ (c : ℕ) (h1 : c < w) (h2 : c < w'), c < 130 → Q ⟨c, h1⟩ = Q' ⟨c, h2⟩) :
    ServeH.cellProvs b nodes orbit chals pubs Q = ServeH.cellProvs b nodes orbit' chals' pubs' Q' := by
  have he := fun i : Fin n => envOfTrace_congrW 130 Q Q' hB hB' hQ orbit.ω orbit'.ω (nodes i)
    (slotVal b 130 chals) (slotVal b 130 pubs) (slotVal b 130 chals') (slotVal b 130 pubs')
  unfold ServeH.cellProvs
  refine List.map_congr_left fun i _ => ?_
  rw [keyVec5_congr 130 _ keyH_read _ _ (he i), he i CellH.mh (by decide)]

end Widths

/-! ## 2. Pole-hit and denominators -/

section Pole
variable {L : Type*} [Field L] [Fintype L] [DecidableEq L] {m : ℕ}

theorem den_of_not_pole (reqs : List (Fin m → L)) (provs : List ((Fin m → L) × L)) (coins : IOCoins L)
    (h : coins.pole ∉ IOPoleHitEvent (recordsW reqs provs) coins.gamma) :
    (∀ r ∈ reqs, compress coins r ≠ 0) ∧ ∀ q ∈ provs, compress coins q.1 ≠ 0 := by
  classical
  refine ⟨fun r hr h0 => h ?_, fun q hq h0 => h ?_⟩
  · simp only [IOPoleHitEvent, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨r, List.mem_append_left _ hr, h0⟩
  · simp only [IOPoleHitEvent, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨q.1, List.mem_append_right _ (by simp [recordsW]; exact ⟨q.2, hq⟩), h0⟩

end Pole

/-! ## 3. The lists at an accepted VSQ coin -/

section Frame
open SVFrameG
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq F]
  [Fintype K] [DecidableEq K] [Fintype F] (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))]
  [DecidableEq (Quad (algebraMap F K δF))] (hT hP kr hC : ℕ)
  {sumC : VerifierData F K hC (shapeVSQ hT hP) → ClaimMsgVS → SummandsVSQ (F := F) (K := K) hT hP hC}
  {sumM : VerifierData F K hC (shapeVSQ hT hP) → Unit → SummandsVSQ (F := F) (K := K) hT hP hC}

local notation "𝕂′" => Quad (algebraMap F K δF)

/-- **At every coin, the projection's coin-free round-0 lists are the VSQ chips' lists.** -/
theorem listsQ_at (V : VerifierData F K hC (shapeVSQ hT hP))
    (msg : MessagesG (compCoreVSQ δF hT hP hC sumC) (memCoreVSQ δF hT hP kr hC sumM)) (χ : Coins frameVSQ K) :
    reqX0 hT hP hC (toVSV hT hP hC V) (projQ hT hP hC (msg.traces χ)) =
        cXQ δF hT hP kr hC V msg χ ++ wXQ δF hT hP kr hC V msg χ ∧
      provX0 hT hP hC (toVSV hT hP hC V) (projQ hT hP hC (msg.traces χ)) = tXQ δF hT hP kr hC V msg χ ∧
      reqP0 hT hP hC (toVSV hT hP hC V) (projQ hT hP hC (msg.traces χ)) = cPQ δF hT hP kr hC V msg χ ∧
      provP0 hT hP hC (toVSV hT hP hC V) (projQ hT hP hC (msg.traces χ)) = wPQ δF hT hP kr hC V msg χ := by
  have hc := compReqs_congrW (K := K) V.computeNodes V.orbitC (fun _ => 0) (fun _ => 0)
    (chalVHQ V.basis χ) (pubVHQ δF V.basis V.claim msg.msg0C (msg.requests χ) χ)
    (projQ hT hP hC (msg.traces χ)).1 (msg.Qc χ) (by show 43 ≤ 70; norm_num) (by show 43 ≤ 85; norm_num)
    (fun _ _ _ _ => rfl)
  have hw := walkLists_congrW V.basis (V.memNodes (tWQ hT hP))
    ((toVSV hT hP hC V).orbitM (tWS hT hP)) (V.orbitM (tWQ hT hP)) (fun _ => 0) (fun _ => 0)
    (chalsVSQ δF χ) (pubsWHQ δF (msg.requests χ) (msg.msg2M χ).1 (msg.msg2M χ).2)
    ((projQ hT hP hC (msg.traces χ)).2 (tWS hT hP)) (msg.Qm χ (tWQ hT hP))
    (by show 25 ≤ 151; norm_num) (by show 25 ≤ 166; norm_num) (fun _ _ _ _ => rfl)
  have ht := cellProvs_congrW V.basis (V.memNodes (tCQ hT hP))
    ((toVSV hT hP hC V).orbitM (tCS hT hP)) (V.orbitM (tCQ hT hP)) (fun _ => 0) (fun _ => 0)
    (chalsVSQ δF χ) (pubsCHQ δF (msg.requests χ) (msg.msg2M χ).1 (msg.msg2M χ).2)
    ((projQ hT hP hC (msg.traces χ)).2 (tCS hT hP)) (msg.Qm χ (tCQ hT hP))
    (by show 130 ≤ 232; norm_num) (by show 130 ≤ 238; norm_num) (fun _ _ _ _ => rfl)
  refine ⟨?_, ht, hc.2, hw.2⟩
  unfold reqX0; exact congrArg₂ (· ++ ·) hc.1 hw.1

/-- The compute twin's consumer budgets. -/
theorem cXQ_len (V : VerifierData F K hC (shapeVSQ hT hP))
    (msg : MessagesG (compCoreVSQ δF hT hP hC sumC) (memCoreVSQ δF hT hP kr hC sumM)) (χ : Coins frameVSQ K)
    (h : AcceptsG V msg χ) :
    (cXQ δF hT hP kr hC V msg χ).length ≤ 3 * V.N ∧ (cPQ δF hT hP kr hC V msg χ).length ≤ 2 * V.N := by
  obtain ⟨hg, hsat⟩ := compute_factsQ δF hT hP kr hC V msg χ h
  have hc : 11 < ringChar F := lt_trans (by norm_num) hg.2.2.1
  have hsel : ∀ i : Fin V.N, ∃ j0, RowSel (rEF V.computeNodes (chalVHQ V.basis χ)
      (pubVHQ δF V.basis V.claim msg.msg0C (msg.requests χ) χ) V.orbitC (msg.Qc χ) i) j0 := fun i =>
    rowSel_of_base (fun t ht => TeleCQ.base_of_satQ V.hN V.computeNodes V.basis δF _ _ V.orbitC _ hsat i t
      (TeleCQ.baseH_sub t ht)) hc
  refine ⟨?_, ?_⟩
  · show (compXReqs _ _ _ _ _).length ≤ _
    unfold compXReqs
    rw [List.length_flatMap]
    calc _ ≤ ((List.finRange V.N).map fun _ => 3).sum := List.sum_le_sum fun i _ => by
            obtain ⟨j0, hs⟩ := hsel i
            exact rowXReqs_len hs
      _ = 3 * V.N := by simp [mul_comm]
  · show (compPReqs _ _ _ _ _).length ≤ _
    unfold compPReqs
    rw [List.length_flatMap]
    calc _ ≤ ((List.finRange V.N).map fun _ => 2).sum := List.sum_le_sum fun i _ => by
            obtain ⟨j0, hs⟩ := hsel i
            exact rowPReqs_len hs
      _ = 2 * V.N := by simp [mul_comm]

/-- Outside the `𝕂′` path summand (at an accepted coin), the three components of the lifted path event
fail at `(γH′, ρH′)`. -/
theorem out_evPQ (V : VerifierData F K hC (shapeVSQ hT hP))
    (msg : MessagesG (compCoreVSQ δF hT hP hC sumC) (memCoreVSQ δF hT hP kr hC sumM)) (χ : Coins frameVSQ K)
    (h : AcceptsG V msg χ) (hPq : ¬ (ioSummandHPQ δF hT hP hC V).mem (msg.traces χ) χ) :
    (gamHQ δF χ, rhoHQ δF χ) ∉ IOFailureEventW
      (liftReqs δF (reqP0 hT hP hC (toVSV hT hP hC V) (projQ hT hP hC (msg.traces χ))))
      (liftProvs δF (provP0 hT hP hC (toVSV hT hP hC V) (projQ hT hP hC (msg.traces χ)))) := by
  rw [mem_ioSummandHPQ] at hPq
  intro hm
  apply hPq
  unfold evPQ
  rw [if_pos]
  · exact hm
  · rw [(listsQ_at δF hT hP kr hC V msg χ).2.2.1]
    exact (cXQ_len δF hT hP kr hC V msg χ h).2

theorem out_evXQ (V : VerifierData F K hC (shapeVSQ hT hP))
    (msg : MessagesG (compCoreVSQ δF hT hP hC sumC) (memCoreVSQ δF hT hP kr hC sumM)) (χ : Coins frameVSQ K)
    (h : AcceptsG V msg χ) (hXq : ¬ (ioSummandHXQ δF hT hP hC V).mem (msg.traces χ) χ) :
    (gamHQ δF χ, rhoHQ δF χ) ∉ IOFailureEventW
      (liftReqs δF (reqX0 hT hP hC (toVSV hT hP hC V) (projQ hT hP hC (msg.traces χ))))
      (liftProvs δF (provX0 hT hP hC (toVSV hT hP hC V) (projQ hT hP hC (msg.traces χ)))) := by
  rw [mem_ioSummandHXQ] at hXq
  intro hm
  apply hXq
  unfold evXQ
  rw [if_pos]
  · exact hm
  · rw [(listsQ_at δF hT hP kr hC V msg χ).1, List.length_append]
    have h1 := (cXQ_len δF hT hP kr hC V msg χ h).1
    have h2 : (wXQ δF hT hP kr hC V msg χ).length = V.memRows (tWS hT hP) := by
      simp [wXQ, ServeH.walkXReqs]; rfl
    omega

/-- The compute path denominators are nonzero at `(γH′, ρH′)` outside the `𝕂′` path summand. -/
theorem cPQ_den (V : VerifierData F K hC (shapeVSQ hT hP))
    (msg : MessagesG (compCoreVSQ δF hT hP hC sumC) (memCoreVSQ δF hT hP kr hC sumM)) (χ : Coins frameVSQ K)
    (h : AcceptsG V msg χ) (hPq : ¬ (ioSummandHPQ δF hT hP hC V).mem (msg.traces χ) χ) :
    ∀ r ∈ cPQ δF hT hP kr hC V msg χ,
      compress (⟨gamHQ δF χ, rhoHQ δF χ⟩ : IOCoins 𝕂′) (BalanceQ.liftRec (L := 𝕂′) r) ≠ 0 := by
  have hout := out_evPQ δF hT hP kr hC V msg χ h hPq
  rw [mem_IOFailureEventW_iff] at hout
  push Not at hout
  have hd := (den_of_not_pole _ _ ⟨gamHQ δF χ, rhoHQ δF χ⟩ hout.2.1).1
  intro r hr
  apply hd
  rw [(listsQ_at δF hT hP kr hC V msg χ).2.2.1]
  exact List.mem_map_of_mem hr

/-- **The `𝕂` path identity** (any `f`): `Σ_{reqP0} f = Σ_{provP0} w · f` at the projection. -/
theorem kP_identity (V : VerifierData F K hC (shapeVSQ hT hP))
    (hV : V.Checks (fun a => reqBoundVSQ hT hP hC V a + internalBoundVSQ hT hP hC V a)
      (ringChar (Quad (algebraMap F K δF))))
    (msg : MessagesG (compCoreVSQ δF hT hP hC sumC) (memCoreVSQ δF hT hP kr hC sumM)) (χ : Coins frameVSQ K)
    (h : AcceptsG V msg χ) (hPq : ¬ (ioSummandHPQ δF hT hP hC V).mem (msg.traces χ) χ)
    (f : (Fin 5 → K) → K) :
    ((reqP0 hT hP hC (toVSV hT hP hC V) (projQ hT hP hC (msg.traces χ))).map f).sum =
      ((provP0 hT hP hC (toVSV hT hP hC V) (projQ hT hP hC (msg.traces χ))).map fun q => q.2 * f q.1).sum := by
  have hout := out_evPQ δF hT hP kr hC V msg χ h hPq
  rw [mem_IOFailureEventW_iff] at hout
  push Not at hout
  obtain ⟨hγ, hpole, hld⟩ := hout
  have hd := den_of_not_pole _ _ ⟨gamHQ δF χ, rhoHQ δF χ⟩ hpole
  obtain ⟨-, -, e3, e4⟩ := listsQ_at δF hT hP kr hC V msg χ
  refine logup_descends (L := 𝕂′) _ _ ⟨gamHQ δF χ, rhoHQ δF χ⟩ hd.1 hd.2 ?_ hγ hld f
  rw [e3, e4]
  simpa only [List.map_map, Function.comp_def] using path_sumQ δF hT hP kr hC V hV msg χ h (cPQ_den δF hT hP kr hC V msg χ h hPq)

/-- **The `𝕂` export identity** (any `f`): `Σ_{reqX0} f = Σ_{provX0} w · f` at the projection. -/
theorem kX_identity (V : VerifierData F K hC (shapeVSQ hT hP))
    (hV : V.Checks (fun a => reqBoundVSQ hT hP hC V a + internalBoundVSQ hT hP hC V a)
      (ringChar (Quad (algebraMap F K δF))))
    (msg : MessagesG (compCoreVSQ δF hT hP hC sumC) (memCoreVSQ δF hT hP kr hC sumM)) (χ : Coins frameVSQ K)
    (h : AcceptsG V msg χ) (hXq : ¬ (ioSummandHXQ δF hT hP hC V).mem (msg.traces χ) χ)
    (hPq : ¬ (ioSummandHPQ δF hT hP hC V).mem (msg.traces χ) χ)
    (f : (Fin 5 → K) → K) :
    ((reqX0 hT hP hC (toVSV hT hP hC V) (projQ hT hP hC (msg.traces χ))).map f).sum =
      ((provX0 hT hP hC (toVSV hT hP hC V) (projQ hT hP hC (msg.traces χ))).map fun q => q.2 * f q.1).sum := by
  have hout := out_evXQ δF hT hP kr hC V msg χ h hXq
  rw [mem_IOFailureEventW_iff] at hout
  push Not at hout
  obtain ⟨hγ, hpole, hld⟩ := hout
  have hd := den_of_not_pole _ _ ⟨gamHQ δF χ, rhoHQ δF χ⟩ hpole
  obtain ⟨e1, e2, -, -⟩ := listsQ_at δF hT hP kr hC V msg χ
  refine logup_descends (L := 𝕂′) _ _ ⟨gamHQ δF χ, rhoHQ δF χ⟩ hd.1 hd.2 ?_ hγ hld f
  rw [e1, e2]
  simpa only [List.map_map, Function.comp_def] using export_sumQ δF hT hP kr hC V hV msg χ h (cPQ_den δF hT hP kr hC V msg χ h hPq)

/-! ## 4. -/

/-- The export consumer guard at an accepted coin. -/
theorem guardX (V : VerifierData F K hC (shapeVSQ hT hP))
    (msg : MessagesG (compCoreVSQ δF hT hP hC sumC) (memCoreVSQ δF hT hP kr hC sumM)) (χ : Coins frameVSQ K)
    (h : AcceptsG V msg χ) :
    (reqX0 hT hP hC (toVSV hT hP hC V) (projQ hT hP hC (msg.traces χ))).length ≤
      3 * (toVSV hT hP hC V).N + (toVSV hT hP hC V).memRows (tWS hT hP) := by
  rw [(listsQ_at δF hT hP kr hC V msg χ).1, List.length_append]
  have h1 := (cXQ_len δF hT hP kr hC V msg χ h).1
  have h2 : (wXQ δF hT hP kr hC V msg χ).length = V.memRows (tWS hT hP) := by
    simp [wXQ, ServeH.walkXReqs]; rfl
  show _ ≤ 3 * V.N + V.memRows (tWS hT hP)
  omega

/-- The path consumer guard at an accepted coin. -/
theorem guardP (V : VerifierData F K hC (shapeVSQ hT hP))
    (msg : MessagesG (compCoreVSQ δF hT hP hC sumC) (memCoreVSQ δF hT hP kr hC sumM)) (χ : Coins frameVSQ K)
    (h : AcceptsG V msg χ) :
    (reqP0 hT hP hC (toVSV hT hP hC V) (projQ hT hP hC (msg.traces χ))).length ≤ 2 * (toVSV hT hP hC V).N := by
  rw [(listsQ_at δF hT hP kr hC V msg χ).2.2.1]
  exact (cXQ_len δF hT hP kr hC V msg χ h).2

/-- **The pole-avoiding `𝕂` coin pair**: at every accepted VSQ coin there is `(γ, ρ) ∈ 𝕂²` outside both
handle IO events of the projection at the transported datum, at which every record of the four handle
lists (every compute consumer, every cell / walk row's key and record) has a nonzero denominator — so
the `𝕂` slot inverses and the memory twins' inverse columns of a re-fill at `(γ, ρ)` exist.  No new
hypothesis: the size facts come from `V.Checks` and `GoodCVSQ`, the pole-freeness from the length
guards (`guardX / guardP`) and the pole-hit component of the events. -/
theorem exists_pair_poleFreeQ (V : VerifierData F K hC (shapeVSQ hT hP))
    (hV : V.Checks (fun a => reqBoundVSQ hT hP hC V a + internalBoundVSQ hT hP hC V a)
      (ringChar (Quad (algebraMap F K δF))))
    (msg : MessagesG (compCoreVSQ δF hT hP hC sumC) (memCoreVSQ δF hT hP kr hC sumM)) (χ : Coins frameVSQ K)
    (h : AcceptsG V msg χ) :
    ∃ γ ρ : K, (γ, ρ) ∉ evX hT hP hC (toVSV hT hP hC V) (projQ hT hP hC (msg.traces χ)) ∧
      (γ, ρ) ∉ evP hT hP hC (toVSV hT hP hC V) (projQ hT hP hC (msg.traces χ)) ∧
      (∀ r ∈ reqX0 hT hP hC (toVSV hT hP hC V) (projQ hT hP hC (msg.traces χ)), compress ⟨γ, ρ⟩ r ≠ 0) ∧
      (∀ q ∈ provX0 hT hP hC (toVSV hT hP hC V) (projQ hT hP hC (msg.traces χ)), compress ⟨γ, ρ⟩ q.1 ≠ 0) ∧
      (∀ r ∈ reqP0 hT hP hC (toVSV hT hP hC V) (projQ hT hP hC (msg.traces χ)), compress ⟨γ, ρ⟩ r ≠ 0) ∧
      (∀ q ∈ provP0 hT hP hC (toVSV hT hP hC V) (projQ hT hP hC (msg.traces χ)), compress ⟨γ, ρ⟩ q.1 ≠ 0) := by
  obtain ⟨hg, -⟩ := compute_factsQ δF hT hP kr hC V msg χ h
  obtain ⟨⟨γ, ρ⟩, hX, hP'⟩ := exists_pair_outsideQ δF hT hP hC V hV hg.2.2.1 (projQ hT hP hC (msg.traces χ))
  have hX' : (γ, ρ) ∉ IOFailureEventW (reqX0 hT hP hC (toVSV hT hP hC V) (projQ hT hP hC (msg.traces χ)))
      (provX0 hT hP hC (toVSV hT hP hC V) (projQ hT hP hC (msg.traces χ))) := by
    intro hm; apply hX; unfold evX; rw [if_pos (guardX δF hT hP kr hC V msg χ h)]; exact hm
  have hP'' : (γ, ρ) ∉ IOFailureEventW (reqP0 hT hP hC (toVSV hT hP hC V) (projQ hT hP hC (msg.traces χ)))
      (provP0 hT hP hC (toVSV hT hP hC V) (projQ hT hP hC (msg.traces χ))) := by
    intro hm; apply hP'; unfold evP; rw [if_pos (guardP δF hT hP kr hC V msg χ h)]; exact hm
  rw [mem_IOFailureEventW_iff] at hX' hP''
  push Not at hX' hP''
  have dX := den_of_not_pole _ _ ⟨γ, ρ⟩ hX'.2.1
  have dP := den_of_not_pole _ _ ⟨γ, ρ⟩ hP''.2.1
  exact ⟨γ, ρ, hX, hP', dX.1, dX.2, dP.1, dP.2⟩

end Frame

end

end Nock.NockVMROM.Thm54.VclL.Handle.DescentVSQ
