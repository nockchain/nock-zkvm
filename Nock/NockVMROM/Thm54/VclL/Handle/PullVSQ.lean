/-
  Nock/NockVMROM/Thm54/VclL/Handle/PullVSQ.lean

* `extQ` / `toVS_extQ` / `extQ_toVS`: the two Im coins re-attached to a fifteen-coin vector;
  * **`pullS`**: a VS summand `s` read at the projection `projQ trQ` and at `toVS χ`, same weight, coins
    `s.coins` mapped into the 17-coin frame, read set `s.dep ∪ {15, 16}` (the projection's round-`≥ 1`
    columns may read the two Im coins, which the fifteen-coin frame does not have); `mem_pullS`:
    `(pullS s).mem trQ χ ↔ s.mem (projQ trQ) (toVS χ)`;
  * the lists `sumCVSQ / sumMVSQ / jointVSQ` (the VS lists at the transported datum `toVSV V`, pulled back,
    with `ioSummandHX / HP` replaced by the four-coin `ioSummandHXQ / HPQ`), and **`epsilonVSQ_eq`**:
    `epsilonOf = boundVCLHQ''`.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.EpsVS
import Nock.NockVMROM.Thm54.VclL.Handle.EpsFigVSQ
import Nock.NockVMROM.Thm54.VclL.Handle.SummandsHQ

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Nock.NockVMROM.Thm54.VclL.Handle.PullVSQ

open Nock Nock.Framework
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.FiniteIO Nock.NockVMROM.Thm54.SVFrame
open Nock.NockVMROM.Thm54.SVFrameG
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.Handle Nock.NockVMROM.Thm54.VclL.Handle.FrameVS
open Nock.NockVMROM.Thm54.VclL.Handle.IOVS Nock.NockVMROM.Thm54.VclL.Handle.FrameVSQ
open Nock.NockVMROM.Thm54.VclL.Handle.ChoiceQ Nock.NockVMROM.Thm54.VclL.Handle.SummandsHQ
open Nock.NockVMROM.Thm54.VclL.Handle.SoundVS Nock.NockVMROM.Thm54.VclL.Handle.EpsVS
open Nock.NockVMROM.Thm54.VclL.Handle.ValIOVS Nock.NockVMROM.Thm54.VclL.Handle.CensusVS
open Nock.NockVMROM.Thm54.VclL.Handle.WalkChainSumVS
open Nock.NockVMROM.Thm54.VclL.Handle.EpsFigVSQ Nock.NockVMROM.Thm54.VclL.Handle.ClaimDenVS
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.T0Tower
open Module
open scoped Polynomial

noncomputable section

/-! ## 1. Coins -/

section Ext
variable {K : Type}

/-- The fifteen VS coins inside the seventeen. -/
def embQ : Fin frameVS.n ↪ Fin frameVSQ.n :=
  ⟨fun i => ⟨i, lt_frameVSQ i⟩, fun _ _ h => Fin.ext (congrArg Fin.val h :)⟩

@[simp] theorem embQ_val (i : Fin frameVS.n) : ((embQ i : Fin frameVSQ.n) : ℕ) = i := rfl

/-- A fifteen-coin vector with the two Im coins `a, b` re-attached. -/
def extQ (ψ : Coins frameVS K) (a b : K) : Coins frameVSQ K :=
  fun i => if h : (i : ℕ) < 15 then ψ ⟨i, h⟩ else if (i : ℕ) = 15 then a else b

theorem toVS_extQ (ψ : Coins frameVS K) (a b : K) : toVS (extQ ψ a b) = ψ := by
  funext i
  have hi : (i : ℕ) < 15 := i.isLt
  simp only [toVS, extQ, dif_pos hi]

theorem extQ_toVS (χ : Coins frameVSQ K) : extQ (toVS χ) (χ cGamHi) (χ cRhoHi) = χ := by
  funext i
  have hi : (i : ℕ) < 17 := i.isLt
  simp only [extQ, toVS]
  split_ifs with h1 h2
  · rfl
  · congr 1; exact Fin.ext (by simp [cGamHi]; omega)
  · congr 1; exact Fin.ext (by simp [cRhoHi]; omega)

theorem embQ_ne_gamHi (i : Fin frameVS.n) : embQ i ≠ cGamHi := by
  intro h; have := congrArg Fin.val h; have hi : (i : ℕ) < 15 := i.isLt
  simp [cGamHi] at this; omega

theorem embQ_ne_rhoHi (i : Fin frameVS.n) : embQ i ≠ cRhoHi := by
  intro h; have := congrArg Fin.val h; have hi : (i : ℕ) < 15 := i.isLt
  simp [cRhoHi] at this; omega

end Ext

/-! ## 2. The pullback of a summand -/

section Pull
variable {F K : Type} [Field F] [Fintype K] [DecidableEq K] (hT hP hC : ℕ)

theorem colRoundM_eq (t : Fin 2) (j : Fin ((shapeVS hT hP).table t).width) :
    ((shapeVSQ hT hP).table t).colRound (Fin.castLE (widthM_le hT hP t) j) =
      ((shapeVS hT hP).table t).colRound j := by
  fin_cases t
  · change colRoundCHQ _ = colRoundCH _
    rfl
  · change colRoundWHQ _ = colRoundWH _
    rfl

/-- A VSQ-staged strategy, projected and read at a fixed pair of Im coins, is VS-staged. -/
theorem staged_proj (Q : Coins frameVSQ K → TrVSQ F hT hP hC)
    (hQ : TracesStaged frameVSQ (tableVSQ hC) (shapeVSQ hT hP) Q) (a b : K) :
    TracesStaged frameVS (tableVS hC) (shapeVS hT hP) (fun ψ => projQ hT hP hC (Q (extQ ψ a b))) := by
  have hco : ∀ (ψ ψ' : Coins frameVS K) (r : ℕ), (∀ i : Fin frameVS.n, frameVS.sampledAfter i < r → ψ i = ψ' i) →
      ∀ i : Fin frameVSQ.n, frameVSQ.sampledAfter i < r → extQ ψ a b i = extQ ψ' a b i := by
    intro ψ ψ' r h i hi
    by_cases h1 : (i : ℕ) < 15
    · simp only [extQ, dif_pos h1]
      refine h _ ?_
      rw [toVS_sampled]
      exact hi
    · simp only [extQ, dif_neg h1]
  refine ⟨fun j ψ ψ' h => ?_, fun t j ψ ψ' h => ?_⟩
  · exact hQ.1 (Fin.castLE (widthC_le hC) j) _ _ (hco ψ ψ' _ h)
  · exact hQ.2 t (Fin.castLE (widthM_le hT hP t) j) _ _ (hco ψ ψ' _ (by
      rw [colRoundM_eq hT hP t j]; exact h))

/-- **A VS summand pulled back to the 17-coin frame**: read at the projection and the first fifteen
coins, read set enlarged by the two Im coins. -/
def pullS (s : BadSummand frameVS K (TrVS F hT hP hC) (TracesStaged frameVS (tableVS hC) (shapeVS hT hP))) :
    BadSummand frameVSQ K (TrVSQ F hT hP hC) (TracesStaged frameVSQ (tableVSQ hC) (shapeVSQ hT hP)) where
  coins := s.coins.map embQ
  dep := s.dep.map embQ ∪ {cGamHi, cRhoHi}
  disj := by
    rw [Finset.disjoint_union_right]
    refine ⟨(Finset.disjoint_map embQ).mpr s.disj, ?_⟩
    rw [Finset.disjoint_left]
    intro x hx hx'
    obtain ⟨i, -, rfl⟩ := Finset.mem_map.mp hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx'
    rcases hx' with h | h
    · exact embQ_ne_gamHi i h
    · exact embQ_ne_rhoHi i h
  badSet trQ χ := Finset.univ.filter fun v : (s.coins.map embQ) → K =>
    (fun i : s.coins => v ⟨embQ i, Finset.mem_map_of_mem _ i.2⟩) ∈ s.badSet (projQ hT hP hC trQ) (toVS χ)
  weight := s.weight
  card_le trQ χ := by
    refine le_trans (Finset.card_le_card_of_injOn
      (fun v : (s.coins.map embQ) → K => fun i : s.coins => v ⟨embQ i, Finset.mem_map_of_mem _ i.2⟩) ?_ ?_)
      (s.card_le (projQ hT hP hC trQ) (toVS χ))
    · intro v hv
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hv
      exact hv
    · intro v _ v' _ h
      funext x
      obtain ⟨i, hi, hix⟩ := Finset.mem_map.mp x.2
      have := congrFun h ⟨i, hi⟩
      have hx : x = ⟨embQ i, Finset.mem_map_of_mem _ hi⟩ := Subtype.ext hix.symm
      rw [hx]; exact this
  readsOn Q hQ χ χ' hχ := by
    have ha : χ cGamHi = χ' cGamHi := hχ _ (Finset.mem_union_right _ (by simp))
    have hb : χ cRhoHi = χ' cRhoHi := hχ _ (Finset.mem_union_right _ (by simp))
    have hr := s.readsOn _ (staged_proj hT hP hC Q hQ (χ cGamHi) (χ cRhoHi)) (toVS χ) (toVS χ')
      (fun j hj => hχ (embQ j) (Finset.mem_union_left _ (Finset.mem_map_of_mem _ hj)))
    simp only at hr
    rw [extQ_toVS, ha, hb, extQ_toVS] at hr
    show Finset.univ.filter _ = Finset.univ.filter _
    rw [hr]

variable (s : BadSummand frameVS K (TrVS F hT hP hC) (TracesStaged frameVS (tableVS hC) (shapeVS hT hP)))

theorem mem_pullS (trQ : TrVSQ F hT hP hC) (χ : Coins frameVSQ K) :
    (pullS hT hP hC s).mem trQ χ ↔ s.mem (projQ hT hP hC trQ) (toVS χ) := by
  unfold BadSummand.mem
  show _ ∈ Finset.univ.filter _ ↔ _
  exact ⟨fun h => (Finset.mem_filter.1 h).2, fun h => Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩⟩

theorem pullS_coins_card : (pullS hT hP hC s).coins.card = s.coins.card := Finset.card_map _

theorem pullS_weight : (pullS hT hP hC s).weight = s.weight := rfl

end Pull

/-! ## 3. The VSQ summand lists -/

section Lists
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq F]
  [Fintype K] [DecidableEq K] [Fintype F] (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))]
  [DecidableEq (Quad (algebraMap F K δF))] (hT hP kr hC : ℕ)
  [Fact (ringChar F).Prime] [Algebra (ZMod (ringChar F)) K]

attribute [local instance] ClaimDenVS.quadCharF

/-- **The VSQ compute summands**: the compute walk and its tiling, pulled back. -/
def sumCVSQ (V : VerifierData F K hC (shapeVSQ hT hP)) (_x : ClaimMsgVS) : SummandsVSQ (F := F) (K := K) hT hP hC :=
  [pullS hT hP hC (cwalkVS hT hP hC (toVSV hT hP hC V)), pullS hT hP hC (ctileVS hT hP hC (toVSV hT hP hC V))]

/-- **The VSQ memory summands**: dyck roots, walk chain, fingerprint export, pulled back. -/
def sumMVSQ (V : VerifierData F K hC (shapeVSQ hT hP)) (_y : Unit) : SummandsVSQ (F := F) (K := K) hT hP hC :=
  [pullS hT hP hC (dyckVS δF hT hP hC (toVSV hT hP hC V)),
    pullS hT hP hC (walkChainVS δF hT hP kr hC (toVSV hT hP hC V)),
    pullS hT hP hC (fpExportIOVS δF hT hP kr hC (toVSV hT hP hC V))]

/-- **The VSQ joint summands**: zero seed, census, validity IO (pulled back), and the two `𝕂′`
handle IO summands on the four coins `{11, 15, 12, 16}`. -/
def jointVSQ (V : VerifierData F K hC (shapeVSQ hT hP)) (x : ClaimMsgVS) (_y : Unit) :
    SummandsVSQ (F := F) (K := K) hT hP hC :=
  [pullS hT hP hC (zeroVS δF hT hP hC), pullS hT hP hC (censusVS δF hT hP hC (toVSV hT hP hC V)),
    pullS hT hP hC (valSummand δF hT hP hC (toVSV hT hP hC V) x), ioSummandHXQ δF hT hP hC V,
    ioSummandHPQ δF hT hP hC V]

/-! ## 4. `ε` -/

/-- **The `ε` of the VSQ lists is `boundVCLHQ''`** (an equality). -/
theorem epsilonVSQ_eq (V : VerifierData F K hC (shapeVSQ hT hP))
    (msg : MessagesG (compCoreVSQ δF hT hP hC (sumCVSQ hT hP hC))
      (memCoreVSQ δF hT hP kr hC (sumMVSQ δF hT hP kr hC))) :
    epsilonOf (allSummandsG (CC := compCoreVSQ δF hT hP hC (sumCVSQ hT hP hC))
        (MC := memCoreVSQ δF hT hP kr hC (sumMVSQ δF hT hP kr hC)) V msg.msg0C msg.msg0M (jointVSQ δF hT hP hC)) =
      boundVCLHQ'' (Fintype.card K) (Fintype.card (Quad (algebraMap F K δF))) V.N
        (V.memRows (tCQ hT hP)) (V.memRows (tWQ hT hP)) (claimFuel V.claim) := by
  have hc : (Fintype.card K : ℚ) ≠ 0 := by
    have := Fintype.card_pos (α := K); positivity
  set V' := toVSV hT hP hC V
  have h2 : ∀ (i j : Fin frameVS.n), i ≠ j → ({i, j} : Finset (Fin frameVS.n)).card = 2 :=
    fun i j h => Finset.card_pair h
  have hL : allSummandsG (CC := compCoreVSQ δF hT hP hC (sumCVSQ hT hP hC))
        (MC := memCoreVSQ δF hT hP kr hC (sumMVSQ δF hT hP kr hC)) V msg.msg0C msg.msg0M (jointVSQ δF hT hP hC) =
      [pullS hT hP hC (cwalkVS hT hP hC V'), pullS hT hP hC (ctileVS hT hP hC V'),
        pullS hT hP hC (dyckVS δF hT hP hC V'), pullS hT hP hC (walkChainVS δF hT hP kr hC V'),
        pullS hT hP hC (fpExportIOVS δF hT hP kr hC V'), pullS hT hP hC (zeroVS δF hT hP hC),
        pullS hT hP hC (censusVS δF hT hP hC V'), pullS hT hP hC (valSummand δF hT hP hC V' msg.msg0C),
        ioSummandHXQ δF hT hP hC V, ioSummandHPQ δF hT hP hC V] := rfl
  rw [hL]
  simp only [epsilonOf, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, pullS_coins_card,
    pullS_weight]
  have e1 : (cwalkVS hT hP hC V').coins.card = 2 := h2 _ _ (by decide)
  have e2 : (ctileVS hT hP hC V').coins.card = 1 := Finset.card_singleton _
  have e3 : (dyckVS δF hT hP hC V').coins.card = 2 := h2 _ _ (by decide)
  have e4 : (walkChainVS δF hT hP kr hC V').coins.card = 2 := h2 _ _ (by decide)
  have e5 : (fpExportIOVS δF hT hP kr hC V').coins.card = 4 := ioSpecVS_dep_card (algebraMap F K δF)
  have e6 : (zeroVS δF hT hP hC (K := K)).coins.card = 2 := h2 _ _ (by decide)
  have e7 : (censusVS δF hT hP hC V').coins.card = 2 := h2 _ _ (by decide)
  have e8 : (valSummand δF hT hP hC V' msg.msg0C).coins.card = 4 := ioSpecVS_dep_card (algebraMap F K δF)
  have e9 : (ioSummandHXQ δF hT hP hC V).coins.card = 4 := ioSpecHQ_dep_card (K := K) δF
  have e10 : (ioSummandHPQ δF hT hP hC V).coins.card = 4 := ioSpecHQ_dep_card (K := K) δF
  rw [e1, e2, e3, e4, e5, e6, e7, e8, e9, e10]
  have w1 : (cwalkVS hT hP hC V').weight = Fintype.card K * (6 * V.N) := rfl
  have w2 : (ctileVS hT hP hC V').weight = 2 * V.N + 2 := rfl
  have w3 : (dyckVS δF hT hP hC V').weight = V.memRows (tCQ hT hP) * (2 * fuelChip - 1) := rfl
  have w4 : (walkChainVS δF hT hP kr hC V').weight = Fintype.card K * (15 * V.memRows (tWQ hT hP)) := rfl
  have w5 : (fpExportIOVS δF hT hP kr hC V').weight =
      ioFailureUnionBound 11 (V.memRows (tWQ hT hP)) (2 * V.memRows (tCQ hT hP))
        (Fintype.card (Quad (algebraMap F K δF))) := rfl
  have w6 : (zeroVS δF hT hP hC (K := K)).weight = 1 := rfl
  have w7 : (censusVS δF hT hP hC V').weight =
      pairCount (V.memRows (tCQ hT hP) + 3) * (2 * claimFuel V.claim - 1) := rfl
  have w8 : (valSummand δF hT hP hC V' msg.msg0C).weight =
      ioFailureUnionBound 5 (3 + 2 * V.memRows (tCQ hT hP)) (V.memRows (tCQ hT hP))
        (Fintype.card (Quad (algebraMap F K δF))) := rfl
  have w9 : (ioSummandHXQ δF hT hP hC V).weight =
      ioFailureUnionBound 5 (3 * V.N + V.memRows (tWQ hT hP)) (V.memRows (tCQ hT hP))
        (Fintype.card (Quad (algebraMap F K δF))) := rfl
  have w10 : (ioSummandHPQ δF hT hP hC V).weight =
      ioFailureUnionBound 5 (2 * V.N) (2 * V.memRows (tWQ hT hP)) (Fintype.card (Quad (algebraMap F K δF))) := rfl
  rw [w1, w2, w3, w4, w5, w6, w7, w8, w9, w10]
  unfold boundVCLHQ''
  push_cast
  field_simp
  ring

end Lists

end

end Nock.NockVMROM.Thm54.VclL.Handle.PullVSQ
