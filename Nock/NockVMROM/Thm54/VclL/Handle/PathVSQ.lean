/-
  Nock/NockVMROM/Thm54/VclL/Handle/PathVSQ.lean

* `denKeyQ_ev'`: `denKeyQ_ev` for keys of length `≤ 5` (the walk records `recLH / recRH` have length 4,
    padded by `keyVec5`'s default `const 0`);
  * `walk_provs_denQ` / `walk_provs_sumQ`: the walk twin's provided handle walk records, weighted by
    `mL / mR`, sum to its terminal `(pub₆, pub₇)` at the `𝕂′` coins;
  * **`path_sumQ`**: at every `AcceptsG`-accepted VSQ coin, with nonzero compute path denominators,
    `Σ_{compP} compress′(lift r)⁻¹ = Σ_{walkP} w · compress′(lift rec)⁻¹` at `(γH′, ρH′)` (both `= ρ₄`).
-/
import Nock.NockVMROM.Thm54.VclL.Handle.BalanceVSQ

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Nock.NockVMROM.Thm54.VclL.Handle.PathVSQ

open Nock Nock.Reified Nock.Framework Module Polynomial
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.T0Tower Nock.NockVMROM.Thm54.FiniteIO Nock.NockVMROM.Thm54.SVFrame
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.VclL.Compute.LogUp
open Nock.NockVMROM.Thm54.VclL.Handle Nock.NockVMROM.Thm54.VclL.Handle.FrameVS
open Nock.NockVMROM.Thm54.VclL.Handle.FrameVSQ Nock.NockVMROM.Thm54.VclL.Handle.ChipH
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHQ Nock.NockVMROM.Thm54.VclL.Handle.BalanceQ
open Nock.NockVMROM.Thm54.VclL.Handle.TeleHQ Nock.NockVMROM.Thm54.VclL.Handle.BalanceVSQ
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler

noncomputable section

/-! ## 1. Short keys -/

section Den
variable {F K : Type} [Field F] [Field K] [Algebra F K] [Fintype K] (δF : F)
  [Fact (¬ IsSquare (algebraMap F K δF))]

local notation "𝕂′" => Quad (algebraMap F K δF)

/-- **`denKeyQ_ev` for keys of length `≤ 5`** (padded by `keyVec5`'s default `const 0`). -/
theorem denKeyQ_ev' (eK : Env K) (eF : Env F) (l : List (CoeffExpr F)) (hl : l.length ≤ 5) :
    (HQ.denKeyQ δF l).ev δF eK eF =
      compress (coinsQ δF eK) (liftRec (K := K) (L := 𝕂′) (ServeH.keyVec5 l eF)) := by
  simp only [HQ.denKeyQ, ev_add, HQ.rhoQ, ev_chal, rlcQ_ev, compress, Walk.rlc, coinsQ, zero_add]
  congr 1
  set g : ℕ → 𝕂′ := fun c => (Quad.mk _ (eK.chal 33) (eK.chal 35)) ^ c *
    liftQ δF ((l.getD c (.const 0)).eval eF) with hg
  have hR : (∑ c : Fin 5, (Quad.mk _ (eK.chal 33) (eK.chal 35)) ^ (c : ℕ) *
      liftRec (K := K) (L := 𝕂′) (ServeH.keyVec5 l eF) c) = ∑ c ∈ Finset.range 5, g c := by
    rw [← Fin.sum_univ_eq_sum_range g 5]
    rfl
  rw [hR, ← Finset.sum_subset (Finset.range_subset_range.mpr hl)]
  intro c _ hc
  rw [Finset.mem_range, not_lt] at hc
  simp only [hg, List.getD_eq_default _ _ hc, CoeffExpr.eval, liftQ, map_zero, mul_zero]

end Den

/-! ## 2. The walk twin's path providers at `𝕂′` -/

section Walk
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [Fintype K]
  (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))] (kroots : ℕ) (b : Basis (Fin 3) F K) {h n : ℕ}
  (hn : 0 < n) (nodes : Fin n → F) (orbit : StrictOrbitDomain F 3 h) (chals pubs : ℕ → K)

local notation "𝕂′" => Quad (algebraMap F K δF)

theorem wDenQ_eq4 (Q : Fin (walkChipHQ δF kroots b hn nodes orbit chals pubs).rap.w → F[X])
    (l : List (CoeffExpr F)) (hl : l.length ≤ 5) (i : Fin n) :
    wDenQ δF kroots b nodes orbit chals pubs Q l i =
      compress (mcoins δF chals)
        (liftRec (K := K) (L := 𝕂′) (ServeH.keyVec5 l (qwEF b nodes orbit chals pubs Q i))) := by
  rw [wDenQ, denKeyQ_ev' δF _ _ _ hl]
  simp only [coinsQ, qwEK_chal]

theorem walk_provs_denQ (Q : Fin (walkChipHQ δF kroots b hn nodes orbit chals pubs).rap.w → F[X])
    (hsat : (walkChipHQ δF kroots b hn nodes orbit chals pubs).rap.Satisfies Q) :
    ∀ q ∈ ServeH.walkPProvs b nodes orbit chals pubs Q,
      compress (mcoins δF chals) (BalanceQ.liftRec (L := 𝕂′) q.1) ≠ 0 := by
  intro q hq
  obtain ⟨j, -, hj⟩ := List.mem_flatMap.mp hq
  have hi := walkHQ_inv δF kroots b hn nodes orbit chals pubs Q hsat j
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
  rcases hj with rfl | rfl
  · rw [← wDenQ_eq4 δF kroots b hn nodes orbit chals pubs Q _ (by simp [WalkHC.recLH])]; exact hi.2.1.1
  · rw [← wDenQ_eq4 δF kroots b hn nodes orbit chals pubs Q _ (by simp [WalkHC.recRH])]; exact hi.2.2.1

/-- **The walk's provided handle walk records, weighted, sum to its terminal `(pub₆, pub₇)`.** -/
theorem walk_provs_sumQ (Q : Fin (walkChipHQ δF kroots b hn nodes orbit chals pubs).rap.w → F[X])
    (hsat : (walkChipHQ δF kroots b hn nodes orbit chals pubs).rap.Satisfies Q)
    (hbind : (walkChipHQ δF kroots b hn nodes orbit chals pubs).BindsPreprocessing Q)
    (hinj : Function.Injective nodes)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω) :
    ((ServeH.walkPProvs b nodes orbit chals pubs Q).map fun q =>
        algebraMap K 𝕂′ q.2 * (compress (mcoins δF chals) (BalanceQ.liftRec (L := 𝕂′) q.1))⁻¹).sum =
      Quad.mk _ (pubs WalkHQ.pubPQ) (pubs (WalkHQ.pubPQ + 1)) := by
  rw [← TeleHQ.walkHQ_telescopeP δF kroots b hn nodes orbit chals pubs Q hsat hbind hinj hadj]
  simp only [ServeH.walkPProvs, map_flatMap_sum, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    add_zero, Function.comp_def]
  rw [Chips.ChipRAP.sum_finRange]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hi := walkHQ_inv δF kroots b hn nodes orbit chals pubs Q hsat j
  rw [wPTermQ, hi.2.1.2, hi.2.2.2, wDenQ_eq4 δF kroots b hn nodes orbit chals pubs Q _ (by simp [WalkHC.recLH]),
    wDenQ_eq4 δF kroots b hn nodes orbit chals pubs Q _ (by simp [WalkHC.recRH])]

end Walk

/-! ## 3. The `𝕂′` path identity at an accepted VSQ coin -/

section Frame
open SVFrameG
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq F]
  [Fintype K] [DecidableEq K] [Fintype F] (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))]
  [DecidableEq (Quad (algebraMap F K δF))] (hT hP kr hC : ℕ)
  {sumC : VerifierData F K hC (shapeVSQ hT hP) → ClaimMsgVS → SummandsVSQ (F := F) (K := K) hT hP hC}
  {sumM : VerifierData F K hC (shapeVSQ hT hP) → Unit → SummandsVSQ (F := F) (K := K) hT hP hC}

local notation "𝕂′" => Quad (algebraMap F K δF)

/-- The VSQ walk twin's provided handle walk records (weights `mL / mR`). -/
abbrev wPQ (V : VerifierData F K hC (shapeVSQ hT hP))
    (msg : MessagesG (compCoreVSQ δF hT hP hC sumC) (memCoreVSQ δF hT hP kr hC sumM)) (χ : Coins frameVSQ K) :
    List ((Fin 5 → K) × K) :=
  ServeH.walkPProvs V.basis (V.memNodes (tWQ hT hP)) (V.orbitM (tWQ hT hP)) (chalsVSQ δF χ)
    (pubsWHQ δF (msg.requests χ) (msg.msg2M χ).1 (msg.msg2M χ).2) (msg.Qm χ (tWQ hT hP))

/-- **The `𝕂′` path LogUp identity at an accepted VSQ coin** (compute path consumers against the
walk twin's weighted path providers, at `(γH′, ρH′)`; both sides are `ρ₄`), given nonzero compute
path denominators. -/
theorem path_sumQ (V : VerifierData F K hC (shapeVSQ hT hP))
    (hV : V.Checks (fun a => reqBoundVSQ hT hP hC V a + internalBoundVSQ hT hP hC V a)
      (ringChar (Quad (algebraMap F K δF))))
    (msg : MessagesG (compCoreVSQ δF hT hP hC sumC) (memCoreVSQ δF hT hP kr hC sumM)) (χ : Coins frameVSQ K)
    (h : AcceptsG V msg χ)
    (hden : ∀ r ∈ cPQ δF hT hP kr hC V msg χ,
      compress (⟨gamHQ δF χ, rhoHQ δF χ⟩ : IOCoins 𝕂′) (BalanceQ.liftRec (L := 𝕂′) r) ≠ 0) :
    ((cPQ δF hT hP kr hC V msg χ).map fun r =>
        (compress (⟨gamHQ δF χ, rhoHQ δF χ⟩ : IOCoins 𝕂′) (BalanceQ.liftRec (L := 𝕂′) r))⁻¹).sum =
      ((wPQ δF hT hP kr hC V msg χ).map fun q =>
        algebraMap K 𝕂′ q.2 * (compress (⟨gamHQ δF χ, rhoHQ δF χ⟩ : IOCoins 𝕂′) (BalanceQ.liftRec (L := 𝕂′) q.1))⁻¹).sum := by
  obtain ⟨hg, hsat⟩ := compute_factsQ δF hT hP kr hC V msg χ h
  obtain ⟨-, hwW, hsatW⟩ := walk_factsQ δF hT hP kr hC V msg χ h
  have hc : 11 < ringChar F := lt_trans (by norm_num) hg.2.2.1
  have hadj : ∀ (i : Fin V.N) (hi : (i : ℕ) + 1 < V.N),
      V.computeNodes ⟨(i : ℕ) + 1, hi⟩ = V.computeNodes i * V.orbitC.ω := fun i hi => by
    rw [hg.1 i hi, mul_comm]
  have hC := TeleCQ.compPQ_sum V.hN V.computeNodes V.basis δF _ _ V.orbitC _ hsat hg.2.1 hadj hc
    (by rw [coinsCV_VSQ]; exact hden)
  erw [coinsCV_VSQ, pubP_VSQ] at hC
  have hWp := walk_provs_sumQ δF kr V.basis (V.hM _) (V.memNodes _) (V.orbitM _) _ _ _ hsatW.1 hsatW.2
    (hV.memNodes_injective _) (hV.hadjM _)
  rw [mcoins, chalsVSQ_coins, pubsWHQ_termP] at hWp
  exact hC.trans hWp.symm

end Frame

end

end Nock.NockVMROM.Thm54.VclL.Handle.PathVSQ
