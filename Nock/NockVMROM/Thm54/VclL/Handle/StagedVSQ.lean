/-
  Nock/NockVMROM/Thm54/VclL/Handle/StagedVSQ.lean

  Additive: a NEW module.

  The compute table has rounds `0 / 1` only, so a
  read of `pub` there would be unstaged.  It is not: the slot numerator / denominator `slotAR / slotDR` read
  their base environment only through `evalQ x.act`, `evalQ (cc fl)` and `evalMQ (den r)`, and none of these
  reads a public value (`slots_act_npub`, by `decide`; `den_rdsF_trace`).

  * §1 `slotAR_npub` / `slotDR_npub` / `slotIQ_pub` / **`compTraceQ_pub`**: the honest `𝕂′` compute column
    function does not depend on the public vector;
  * §2 coin reads: `chalVHQ` reads coins `11..16` only (all sampled after round 0);
  * §3 **`qcVSQ_staged`**: the compute trace — columns `< 43` coin-free, columns `43..84` read only the
    round-0-sampled coins `11..16`;
  * **`msgVSQ_staged`**: `TracesStaged frameVSQ (tableVSQ hC) (shapeVSQ hT hP) (msgVSQ H t x).traces`.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.HonestOfRunVSQ
import Nock.NockVMROM.Thm54.VclL.Handle.HonestCongH

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.FrameVSQ

open Nock Nock.Reified Nock.Framework Nock.Walk
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.SVFrame Nock.NockVMROM.Thm54.SVFrameG
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.Handle Nock.NockVMROM.Thm54.VclL.Handle.FrameVS
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.VclL.GenWalk Nock.NockVMROM.Thm54.TraceGen
open Nock.NockVMROM.Thm54.VclL.Compute.LogUp
open Nock.NockVMROM.Thm54.VclL.Handle.ChipH
open Module
open scoped Polynomial

noncomputable section

/-! ## 1. The slot terms read no public value -/

/-- A variable that is not a public value. -/
def npub : VarKind × ℕ → Bool
  | (.publicVal, _) => false
  | _ => true

/-- **The slot activities read no public value** (`decide` over the three slot specifications). -/
theorem slots_act_npub :
    ∀ S ∈ [slot0 (F := ℚ), slot1, slot2], ∀ x ∈ S.ents, ∀ p ∈ rdsQ x.act, npub p = true := by
  decide

theorem rlcKey_rdsF_trace (γ : ℕ) :
    ∀ (r : List ℕ) (m : ℕ), ∀ p ∈ rdsF (rlcKey (F := ℚ) .traceCur γ m r), npub p = true
  | [], m => by simp [rlcKey, rdsF]
  | i :: r, m => by
    intro p hp
    simp only [rlcKey, rdsF, rdsQ, List.mem_append, List.nil_append, List.mem_singleton] at hp
    rcases hp with rfl | hp
    · rfl
    · exact rlcKey_rdsF_trace γ r (m + 1) p hp

/-- **A record denominator reads no public value** (base side: current-row columns only). -/
theorem den_rdsF_npub (r : List ℕ) : ∀ p ∈ rdsF (ChipH.den (F := ℚ) r), npub p = true := by
  intro p hp
  simp only [ChipH.den, rdsF, List.nil_append] at hp
  exact rlcKey_rdsF_trace _ r 0 p hp

section PubFree
variable {F K : Type} [Field F] [Field K] [Algebra F K]

theorem envRd_npub (e1 e2 : Env F) (ht : e1.trace = e2.trace) (hn : e1.traceNext = e2.traceNext)
    (hc : e1.chal = e2.chal) (p : VarKind × ℕ) (hp : npub p = true) : envRd e1 p = envRd e2 p := by
  obtain ⟨k, i⟩ := p
  cases k
  · exact congrFun ht i
  · exact congrFun hn i
  · exact congrFun hc i
  · exact absurd hp (by simp [npub])

theorem evalQ_npub (g : CoeffExpr ℚ) (hg : ∀ p ∈ rdsQ g, npub p = true) (e1 e2 : Env F)
    (ht : e1.trace = e2.trace) (hn : e1.traceNext = e2.traceNext) (hc : e1.chal = e2.chal) :
    evalQ g e1 = evalQ g e2 :=
  evalQ_congr_rds g e1 e2 fun p hp => envRd_npub e1 e2 ht hn hc p (hg p hp)

theorem evalMQ_den_npub (r : List ℕ) (eK : Env K) (e1 e2 : Env F)
    (ht : e1.trace = e2.trace) (hn : e1.traceNext = e2.traceNext) (hc : e1.chal = e2.chal) :
    evalMQ (ChipH.den (F := ℚ) r) eK e1 = evalMQ (ChipH.den (F := ℚ) r) eK e2 :=
  evalMQ_congr_rds _ eK eK e1 e2 (fun _ _ => rfl)
    fun p hp => envRd_npub e1 e2 ht hn hc p (den_rdsF_npub r p hp)

theorem evalQ_cc_npub (fl : ℕ) (e1 e2 : Env F) (ht : e1.trace = e2.trace) :
    evalQ (cc (F := ℚ) fl) e1 = evalQ (cc (F := ℚ) fl) e2 := by
  show e1.trace fl = e2.trace fl
  rw [ht]

/-- **`A` of a slot reads no public value.** -/
theorem slotAR_npub (S : SlotSpec ℚ) (hS : S ∈ [slot0 (F := ℚ), slot1, slot2]) (eK : Env K) (e1 e2 : Env F)
    (ht : e1.trace = e2.trace) (hn : e1.traceNext = e2.traceNext) (hc : e1.chal = e2.chal) :
    slotAR e1 eK S = slotAR e2 eK S := by
  unfold slotAR
  have h1 : (S.ents.map fun x => evalQ x.act e1) = S.ents.map fun x => evalQ x.act e2 :=
    List.map_congr_left fun x hx => evalQ_npub _ (slots_act_npub S hS x hx) e1 e2 ht hn hc
  rw [h1]
  rcases S.pair with _ | ⟨fl, a, b⟩
  · rfl
  · simp only
    rw [evalQ_cc_npub fl e1 e2 ht, evalMQ_den_npub a eK e1 e2 ht hn hc, evalMQ_den_npub b eK e1 e2 ht hn hc]

/-- **`D` of a slot reads no public value.** -/
theorem slotDR_npub (S : SlotSpec ℚ) (hS : S ∈ [slot0 (F := ℚ), slot1, slot2]) (eK : Env K) (e1 e2 : Env F)
    (ht : e1.trace = e2.trace) (hn : e1.traceNext = e2.traceNext) (hc : e1.chal = e2.chal) :
    slotDR e1 eK S = slotDR e2 eK S := by
  unfold slotDR
  have h1 : (S.ents.map fun x => algebraMap F K (evalQ x.act e1) * evalMQ (ChipH.den x.rcd) eK e1) =
      S.ents.map fun x => algebraMap F K (evalQ x.act e2) * evalMQ (ChipH.den x.rcd) eK e2 :=
    List.map_congr_left fun x hx => by
      rw [evalQ_npub _ (slots_act_npub S hS x hx) e1 e2 ht hn hc, evalMQ_den_npub x.rcd eK e1 e2 ht hn hc]
  rw [h1]
  rcases S.pair with _ | ⟨fl, a, b⟩
  · rfl
  · simp only
    rw [evalQ_cc_npub fl e1 e2 ht, evalMQ_den_npub a eK e1 e2 ht hn hc, evalMQ_den_npub b eK e1 e2 ht hn hc]

end PubFree

section CompPub
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [Fintype K] [DecidableEq F]
  (δ : F) [Fact (¬ IsSquare (algebraMap F K δ))] (b : Basis (Fin 3) F K) (cells : List Noun)
  (rows : ℕ → RowN) (N : ℕ) (chalV pubVal pubVal' : ℕ → F) (ln cnt acc : ℕ → K)

/-- **The honest `𝕂′` slot inverse reads no public value.** -/
theorem slotIQ_pub (r : ℕ) (S : SlotSpec ℚ) (hS : S ∈ [slot0 (F := ℚ), slot1, slot2]) :
    HonestCompQ.slotIQ δ b cells rows N chalV pubVal r S = HonestCompQ.slotIQ δ b cells rows N chalV pubVal' r S := by
  unfold HonestCompQ.slotIQ
  rw [slotAR_npub S hS _ (baseEnvC cells rows N chalV pubVal r) (baseEnvC cells rows N chalV pubVal' r) rfl rfl rfl,
    slotDR_npub S hS _ (baseEnvC cells rows N chalV pubVal r) (baseEnvC cells rows N chalV pubVal' r) rfl rfl rfl]

/-- Off the slot-inverse block `43..51`, the base compute column function reads no public value. -/
theorem compTrace_pub_off (r c : ℕ) (hc : ¬ (43 ≤ c ∧ c < 52)) :
    compTrace b cells rows N chalV pubVal ln cnt acc r c = compTrace b cells rows N chalV pubVal' ln cnt acc r c := by
  by_cases h43 : c < 43
  · rw [compTrace_base b cells rows N chalV pubVal ln cnt acc r c h43,
      compTrace_base b cells rows N chalV pubVal' ln cnt acc r c h43]
  · unfold compTrace
    rw [if_neg (show ¬ c < 52 by omega), if_neg (show ¬ c < 52 by omega)]

/-- **The honest `𝕂′` compute column function reads no public value.** -/
theorem compTraceQ_pub (r c : ℕ) :
    HonestCompQ.compTraceQ δ b cells rows N chalV pubVal ln cnt acc r c =
      HonestCompQ.compTraceQ δ b cells rows N chalV pubVal' ln cnt acc r c := by
  by_cases h43 : c < 43
  · rw [HonestCompQ.compTraceQ_base δ b cells rows N chalV pubVal ln cnt acc r c h43,
      HonestCompQ.compTraceQ_base δ b cells rows N chalV pubVal' ln cnt acc r c h43]
  by_cases hw : 58 ≤ c ∧ c < 70
  · rw [HonestCompQ.compTraceQ_walk δ b cells rows N chalV pubVal ln cnt acc r c hw,
      HonestCompQ.compTraceQ_walk δ b cells rows N chalV pubVal' ln cnt acc r c hw]
    unfold compTrace
    rw [if_neg (show ¬ c < 52 by omega), if_neg (show ¬ c < 52 by omega)]
  by_cases h85 : 85 ≤ c
  · rw [HonestCompQ.compTraceQ_zero δ b cells rows N chalV pubVal ln cnt acc r c h85,
      HonestCompQ.compTraceQ_zero δ b cells rows N chalV pubVal' ln cnt acc r c h85]
  unfold HonestCompQ.compTraceQ
  rw [slotIQ_pub δ b cells rows N chalV pubVal pubVal' r slot0 List.mem_cons_self,
    slotIQ_pub δ b cells rows N chalV pubVal pubVal' r slot1 (List.mem_cons_of_mem _ List.mem_cons_self),
    slotIQ_pub δ b cells rows N chalV pubVal pubVal' r slot2 (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))]
  iterate 10 refine ite_congr rfl (fun _ => rfl) (fun _ => ?_)
  exact compTrace_pub_off b cells rows N chalV pubVal pubVal' ln cnt acc r c (by omega)

end CompPub

/-! ## 2. Coin reads -/

section CoinReads
variable {F K : Type} [Field F] [Field K] [Algebra F K]

theorem frameVSQ_sampled_le_one (i : Fin frameVSQ.n) : frameVSQ.sampledAfter i ≤ 1 := by
  revert i; decide

/-- Coins `11..16` (the handle and walk coins) are sampled after round 0. -/
theorem frameVSQ_sampled_hi (k : ℕ) (hk : k < 17) (h11 : 11 ≤ k) :
    frameVSQ.sampledAfter ⟨k, hk⟩ = 0 := by
  interval_cases k <;> rfl

/-- **`chalVHQ` reads only coins sampled after round 0.** -/
theorem chalVHQ_congr (b : Basis (Fin 3) F K) (χ χ' : Coins frameVSQ K)
    (h0 : ∀ i : Fin frameVSQ.n, frameVSQ.sampledAfter i = 0 → χ i = χ' i) :
    chalVHQ b χ = chalVHQ b χ' := by
  have e : ∀ k (hk : k < 17), 11 ≤ k → χ ⟨k, hk⟩ = χ' ⟨k, hk⟩ :=
    fun k hk h11 => h0 _ (frameVSQ_sampled_hi k hk h11)
  have hc : coinHQ χ = coinHQ χ' := by
    funext q
    unfold coinHQ coinH
    split_ifs
    · exact e 11 (by decide) (by decide)
    · exact e 12 (by decide) (by decide)
    · exact e 13 (by decide) (by decide)
    · exact e 14 (by decide) (by decide)
    · exact e 15 (by decide) (by decide)
    · exact e 16 (by decide) (by decide)
  funext j
  unfold chalVHQ
  rw [hc]

/-- Agreement below a round at `frameVSQ` transfers to the first eleven coins (`frameVCL`). -/
theorem toVCL_toVS_agree (χ χ' : Coins frameVSQ K) (r : ℕ)
    (h : ∀ i : Fin frameVSQ.n, frameVSQ.sampledAfter i < r → χ i = χ' i) :
    ∀ i : Fin frameVCL.n, frameVCL.sampledAfter i < r → toVCL (toVS χ) i = toVCL (toVS χ') i := by
  intro i hi
  rw [toVCL_sampled, toVS_sampled] at hi
  exact h _ hi

end CoinReads

/-! ## 3. The compute trace is staged -/

section CompStaged
variable {F K Kg : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq F]
  [Fintype K] [DecidableEq K] [Fintype F] [Fact (ringChar F).Prime] [Algebra (ZMod (ringChar F)) K]
  [Field Kg] {δF : F} [Fact (¬ IsSquare (algebraMap F K δF))] [DecidableEq (Quad (algebraMap F K δF))]
  {hT hP hC kr : ℕ} (H : HonestVCLW (K := K) δF hT hP hC kr) (t : NTree (GenComputeRow Kg)) (x : ClaimMsgVS)

/-- **The honest `𝕂′` compute trace is staged**: columns `< 43` are coin-free; the round-1 columns read
only `chalVHQ` (coins `11..16`) and the walk coins `13 / 14`, all sampled after round 0 — never the public
vector (`compTraceQ_pub`), hence never `rhoVSQ` (coins `4..7`). -/
theorem qcVSQ_staged : StagedCols frameVSQ (tableVSQ hC).colRound (fun χ => qcVSQ H t x χ) := by
  intro j χ χ' h
  by_cases hj : (j : ℕ) < 43
  · simp only [qcVSQ, HonestCompQ.compPolyQ]
    refine congrArg (fun f => Lagrange.interpolate Finset.univ H.V.computeNodes f) (funext fun i => ?_)
    rw [HonestCompQ.compTraceQ_base _ _ _ _ _ _ _ _ _ _ _ _ hj, HonestCompQ.compTraceQ_base _ _ _ _ _ _ _ _ _ _ _ _ hj]
  · have hr : (tableVSQ hC).colRound j = 1 := by
      show (if (j : ℕ) < ChipH.round0W then 0 else 1) = 1
      rw [if_neg (show ¬ (j : ℕ) < ChipH.round0W from hj)]
    have h0 : ∀ i : Fin frameVSQ.n, frameVSQ.sampledAfter i = 0 → χ i = χ' i :=
      fun i hi => h i (by rw [hr, hi]; exact Nat.zero_lt_one)
    have hcv := chalVHQ_congr H.V.basis χ χ' h0
    have hα : (toVS χ) cAlphaW = (toVS χ') cAlphaW := h0 ⟨13, by decide⟩ rfl
    have hγ : (toVS χ) cGamW = (toVS χ') cGamW := h0 ⟨14, by decide⟩ rfl
    simp only [qcVSQ, HonestCompQ.compPolyQ]
    refine congrArg (fun f => Lagrange.interpolate Finset.univ H.V.computeNodes f) (funext fun i => ?_)
    refine (compTraceQ_pub δF H.V.basis H.d.cells (wRows (fW t)) (fW t).length (chalVHQ H.V.basis χ)
      (pubVHQ δF H.V.basis H.V.claim x (rhoVSQ H t χ) χ) (pubVHQ δF H.V.basis H.V.claim x (rhoVSQ H t χ') χ')
      _ _ _ _ _).trans ?_
    rw [hcv, hα, hγ]

end CompStaged

/-! ## 4. The twins are staged -/

section MemStaged
variable {F K Kg : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq F]
  [Fintype K] [DecidableEq K] [Fintype F] [Fact (ringChar F).Prime] [Algebra (ZMod (ringChar F)) K]
  [Field Kg] {δF : F} [Fact (¬ IsSquare (algebraMap F K δF))] [DecidableEq (Quad (algebraMap F K δF))]
  {hT hP hC kr : ℕ} (H : HonestVCLW (K := K) δF hT hP hC kr) (t : NTree (GenComputeRow Kg)) (x : ClaimMsgVS)

/-- **The `𝕂′` cell twin's round-0 / round-1 columns** (`< 184`): base columns `< 129` coin-free, `129 = mh`
coin-free, the shifted round-1 roles `130..183` read only the seed coins `2, 3` (`zC`). -/
theorem qCell_col_congr (bs : List Noun) (χ χ' : Coins frameVSQ K) (mhv : Fin (H.V.memRows (tCW hT hP)) → F)
    (iv av iv' av' : Fin (H.V.memRows (tCW hT hP)) → Quad (algebraMap F K δF)) (j : ℕ) (hj : j < 184)
    (h1 : 130 ≤ j → ∀ i : Fin frameVSQ.n, frameVSQ.sampledAfter i < 1 → χ i = χ' i) :
    CellTraceHQ.colHQ δF H.V.basis (cellColB H bs (toVCL (toVS χ))) mhv iv av j =
      CellTraceHQ.colHQ δF H.V.basis (cellColB H bs (toVCL (toVS χ'))) mhv iv' av' j := by
  funext i
  have hW : (cellTemplate δF).width 3 = 225 := CellTraceH.cellTemplate_width δF
  simp only [CellTraceHQ.colHQ, extColF, hW]
  by_cases h129 : j < 129
  · rw [if_pos h129, if_pos h129]
    unfold cellColB
    exact cellCol_round1 H.V.basis _ _ _ _ _ _ j (fun i k => cellRows0_base_indep _ _ _ _ _ _ i k)
      (fun h => absurd h (by omega)) i (by omega)
  · rw [if_neg h129, if_neg h129]
    by_cases h130 : j < 130
    · rw [if_pos h130, if_pos h130]
      have : j = 129 := by omega
      subst this
      simp [CellTraceHQ.new]
    · rw [if_neg h130, if_neg h130, if_pos (by omega), if_pos (by omega)]
      have hz := zC_congr (δF := δF) (toVCL (toVS χ)) (toVCL (toVS χ')) (r := 1) le_rfl
        (toVCL_toVS_agree χ χ' 1 (h1 (by omega)))
      unfold cellColB
      refine cellCol_round1 H.V.basis _ _ _ _ _ _ (j - (130 - 129))
        (fun i k => cellRows0_base_indep _ _ _ _ _ _ i k) (fun _ i' s _ => ?_) i (by omega)
      show (cellRowsB H bs (zC (toVCL (toVS χ))) i').qslot s = (cellRowsB H bs (zC (toVCL (toVS χ'))) i').qslot s
      rw [hz]

/-- **The `𝕂′` walk twin's round-0 / round-1 columns** (`< 97`): base `< 21` coin-free, `kL vL kR vR` at
`21..24` coin-free, the shifted round-1 roles `25..96` read only the seed coins `2, 3`. -/
theorem qWalk_col_congr (χ χ' : Coins frameVSQ K) (kLv vLv kRv vRv : Fin (H.V.memRows (tWW hT hP)) → F)
    (R R' : WalkTraceH.Roles (H.V.memRows (tWW hT hP)) (Quad (algebraMap F K δF))) (j : ℕ) (hj : j < 97)
    (h1 : 25 ≤ j → ∀ i : Fin frameVSQ.n, frameVSQ.sampledAfter i < 1 → χ i = χ' i) :
    WalkTraceHQ.colHQ δF kr H.V.basis (walkColVS H (toVS χ)) kLv vLv kRv vRv R j =
      WalkTraceHQ.colHQ δF kr H.V.basis (walkColVS H (toVS χ')) kLv vLv kRv vRv R' j := by
  funext i
  have hW : (walkTemplate δF kr).width 3 = 132 := WalkTraceH.walkTemplate_width δF kr
  simp only [WalkTraceHQ.colHQ, extColF, hW]
  by_cases h21 : j < 21
  · rw [if_pos h21, if_pos h21]
    simp only [walkColVS, walkCol, if_pos h21]
    rfl
  · rw [if_neg h21, if_neg h21]
    by_cases h25 : j < 25
    · rw [if_pos h25, if_pos h25]
      unfold WalkTraceHQ.new
      have : j = 21 ∨ j = 22 ∨ j = 23 ∨ j = 24 := by omega
      rcases this with rfl | rfl | rfl | rfl <;> simp
    · rw [if_neg h25, if_neg h25, if_pos (by omega), if_pos (by omega)]
      have hz := zC_congr (δF := δF) (toVCL (toVS χ)) (toVCL (toVS χ')) (r := 1) le_rfl
        (toVCL_toVS_agree χ χ' 1 (h1 (by omega)))
      simp only [walkColVS, walkCol, if_neg (show ¬ j - (25 - 21) < 21 by omega)]
      congr 1
      unfold wroleVal
      have hρ : (j - (25 - 21) - 21) / 3 < 24 := by omega
      simp only [hρ, if_true]
      have e : ∀ s, (H.wVals (toVCL (toVS χ)) i).fpSlot s = (H.wVals (toVCL (toVS χ')) i).fpSlot s := by
        intro s
        apply fpSlot_congr <;>
          simp only [HonestVCLW.wVals, HonestVCLW.wRows, walkFill, walkFillInv, walkRow0, hz]
      rw [e]

end MemStaged

/-! ## 5. The honest VSQ message is staged -/

section MsgStaged
variable {F K Kg : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq F]
  [Fintype K] [DecidableEq K] [Fintype F] [Fact (ringChar F).Prime] [Algebra (ZMod (ringChar F)) K]
  [Field Kg] {δF : F} [Fact (¬ IsSquare (algebraMap F K δF))] [DecidableEq (Quad (algebraMap F K δF))]
  {hT hP hC kr : ℕ} (H : HonestVCLW (K := K) δF hT hP hC kr) (t : NTree (GenComputeRow Kg)) (x : ClaimMsgVS)

/-- **`msgVSQ_staged`: the honest VSQ message is staged at `frameVSQ`.**  Every column of every table reads
only coins sampled before its round: compute (`qcVSQ_staged`), the `𝕂′` cell twin (`qCell_col_congr`) and
the `𝕂′` walk twin (`qWalk_col_congr`); round-2 columns read every coin, all sampled after round `≤ 1`. -/
theorem msgVSQ_staged
    {sumC : VerifierData F K hC (shapeVSQ hT hP) → ClaimMsgVS → SummandsVSQ (F := F) (K := K) hT hP hC}
    {sumM : VerifierData F K hC (shapeVSQ hT hP) → Unit → SummandsVSQ (F := F) (K := K) hT hP hC} :
    TracesStaged frameVSQ (tableVSQ hC) (shapeVSQ hT hP) (msgVSQ (sumC := sumC) (sumM := sumM) H t x).traces := by
  refine ⟨qcVSQ_staged H t x, fun tt j χ χ' h => ?_⟩
  show (msgVSQ (sumC := sumC) (sumM := sumM) H t x).Qm χ tt j = (msgVSQ (sumC := sumC) (sumM := sumM) H t x).Qm χ' tt j
  by_cases h2 : 2 ≤ ((shapeVSQ hT hP).table tt).colRound j
  · have : χ = χ' := funext fun c => h c (by have := frameVSQ_sampled_le_one c; omega)
    subst this; rfl
  simp only [msgVSQ]
  by_cases ht : (tt : ℕ) = 0
  · rw [dif_pos ht, dif_pos ht]
    obtain rfl : tt = tCQ hT hP := Fin.ext ht
    have hr : ((shapeVSQ hT hP).table (tCQ hT hP)).colRound j = colRoundCHQ ⟨j, j.2⟩ := rfl
    rw [hr] at h h2
    have hj : (j : ℕ) < 184 := by
      by_contra hc; apply h2; simp only [colRoundCHQ]; rw [if_neg (by omega), if_neg (by omega)]
    unfold qCellVSQ CellTraceHQ.cellTraceHQ
    refine honestQ_congr _ _ _ _ _ _ ?_
    refine qCell_col_congr H _ χ χ' _ _ _ _ _ _ hj (fun h130 i hi => h i ?_)
    change 130 ≤ (j : ℕ) at h130
    simp only [colRoundCHQ]; rw [if_neg (by omega), if_pos (by simpa using hj)]; exact hi
  · rw [dif_neg ht, dif_neg ht]
    obtain rfl : tt = tWQ hT hP := Fin.ext (by have := tt.2; change (tt : ℕ) < 2 at this; show (tt : ℕ) = 1; omega)
    have hr : ((shapeVSQ hT hP).table (tWQ hT hP)).colRound j = colRoundWHQ ⟨j, j.2⟩ := rfl
    rw [hr] at h h2
    have hj : (j : ℕ) < 97 := by
      by_contra hc; apply h2; simp only [colRoundWHQ]; rw [if_neg (by omega), if_neg (by omega)]
    unfold qWalkVSQ WalkTraceHQ.walkTraceHQ
    refine honestQ_congr _ _ _ _ _ _ ?_
    refine qWalk_col_congr H χ χ' _ _ _ _ _ _ _ hj (fun h25 i hi => h i ?_)
    change 25 ≤ (j : ℕ) at h25
    simp only [colRoundWHQ]; rw [if_neg (by omega), if_pos (by simpa using hj)]; exact hi

end MsgStaged

end

end Nock.NockVMROM.Thm54.VclL.Handle.FrameVSQ
