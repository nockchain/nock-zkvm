/-
  Nock/NockVMROM/Thm54/VclL/Handle/ReadIOJ8.lean

  **The read sets of the J-8 IO lists.**

  Every IO list of `LinkJ8X'`'s readouts `rdX` / `rdP` / `rdS` (the compute requests of the three handle balances,
  the J-8 walk's / J chip's / atom table's / atom walk's / cell table's records) reads ONLY round-0 base columns of
  its chip, and NO coin and NO public:
  * compute `computeChipVCLHX`: columns `< 69` (`slotsX_read`, `consQX_congr`, `compReqsX_congr`);
  * J chip `jetChipJ8`: columns `< 29` (`rowJ_congr`, `jLists_congr`);
  * cell table `cellChipHQKW`: columns `< 134` (`cellProvsW_congr`);
  * atom table `atomChipHQ`: columns `< 205` (`atomIncProvs_congr`);
-/
import Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8P
import Nock.NockVMROM.Thm54.VclL.Handle.DescentVSQ

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxRecDepth 100000

namespace Nock.NockVMROM.Thm54.VclL.Handle.ReadIOJ8

open Nock Nock.Reified Nock.Framework Module Polynomial
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.MonolithicRAP Nock.Framework.Reify
open Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHX
open Nock.NockVMROM.Thm54.VclL.Handle.TeleCQX (consQX pairRecsB)
open Nock.NockVMROM.Thm54.VclL.Handle.DenXJ8 (keyX keyXN compReqsX mOf)
open Nock.NockVMROM.Thm54.VclL.Handle.IOVS (rdOK)

noncomputable section

/-! ## 1. The compute requests read columns `< 69` only -/

/-- A record entry reads a column `< B` (or is a constant). -/
def reLt (B : ℕ) : RE → Bool
  | .col i => decide (i < B)
  | .k _ => true

/-- **The compute slots read only round-0 columns `< 69`**: every entry's activity and record, every pair's flag
and records. -/
theorem slotsX_read : ∀ S ∈ (ChipHX.slotsX : List (SlotX ℚ)), (∀ x ∈ S.ents,
    rdOK 69 x.act = true ∧ x.rcd.all (reLt 69) = true) ∧
    (match S.pair with
     | some (fl, a, c, _) => decide (fl < 69) && a.all (reLt 69) && c.all (reLt 69)
     | none => true) = true := by
  decide

section Cong
variable {F : Type} [Field F]

theorem evalQX_congr (B : ℕ) (g : CoeffExpr ℚ) (hg : rdOK B g = true) (e1 e2 : Env F)
    (h : ∀ c < B, e1.trace c = e2.trace c) : evalQX g e1 = evalQX g e2 := by
  induction g with
  | const c => rfl
  | var k i =>
    cases k with
    | traceCur => simp only [rdOK, decide_eq_true_eq] at hg; exact h i hg
    | traceNext => simp [rdOK] at hg
    | challenge => simp [rdOK] at hg
    | publicVal => simp [rdOK] at hg
  | add a b iha ihb =>
    simp only [rdOK, Bool.and_eq_true] at hg; simp only [evalQX, iha hg.1, ihb hg.2]
  | sub a b iha ihb =>
    simp only [rdOK, Bool.and_eq_true] at hg; simp only [evalQX, iha hg.1, ihb hg.2]
  | mul a b iha ihb =>
    simp only [rdOK, Bool.and_eq_true] at hg; simp only [evalQX, iha hg.1, ihb hg.2]
  | neg a iha => simp only [rdOK] at hg; simp only [evalQX, iha hg]
  | pow a n iha => simp only [rdOK] at hg; simp only [evalQX, iha hg]

theorem reEv_congr (B : ℕ) (x : RE) (hx : reLt B x = true) (e1 e2 : Env F)
    (h : ∀ c < B, e1.trace c = e2.trace c) : x.ev e1.trace = x.ev e2.trace := by
  cases x with
  | col i => simp only [reLt, decide_eq_true_eq] at hx; exact h i hx
  | k c => rfl

variable {K : Type} [Field K] [Algebra F K]

theorem keyX_congr (B : ℕ) (m : ℕ) (r : List RE) (hr : r.all (reLt B) = true) (e1 e2 : Env F)
    (h : ∀ c < B, e1.trace c = e2.trace c) : (keyX m r e1 : Fin m → K) = keyX m r e2 := by
  funext c
  simp only [keyX, keyXN]
  congr 1
  by_cases hc : (c : ℕ) < r.length
  · rw [List.getD_eq_getElem _ _ hc]
    exact reEv_congr B _ (List.all_eq_true.mp hr _ (List.getElem_mem hc)) e1 e2 h
  · rw [List.getD_eq_default _ _ (by omega)]; rfl

variable [DecidableEq F]

/-- **A row's consumed records read only its columns `< 69`.** -/
theorem consQX_congr (e1 e2 : Env F) (h : ∀ c < 69, e1.trace c = e2.trace c) (bl : Bal) :
    consQX e1 bl = consQX e2 bl := by
  unfold consQX
  refine congrArg List.flatten (List.map_congr_left fun S hS => ?_)
  obtain ⟨hE, hP⟩ := slotsX_read S hS
  congr 1
  · congr 1
    refine List.filter_congr fun x hx => ?_
    rw [evalQX_congr 69 _ (hE x (List.mem_filter.mp hx).1).1 e1 e2 h]
  · unfold pairRecsB
    cases hp : S.pair with
    | none => rfl
    | some q =>
      obtain ⟨fl, a, c, b'⟩ := q
      rw [hp] at hP
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hP
      simp only [h fl hP.1.1]

/-- The records of `consQX` read only columns `< 69`. -/
theorem consQX_read (e : Env F) (bl : Bal) : ∀ r ∈ consQX e bl, r.all (reLt 69) = true := by
  intro r hr
  unfold consQX at hr
  obtain ⟨S, hS, hr⟩ := List.mem_flatMap.mp hr
  obtain ⟨hE, hP⟩ := slotsX_read S hS
  rcases List.mem_append.mp hr with hr | hr
  · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hr
    exact (hE x (List.mem_filter.mp (List.mem_filter.mp hx).1).1).2
  · unfold pairRecsB at hr
    cases hp : S.pair with
    | none => rw [hp] at hr; simp at hr
    | some q =>
      obtain ⟨fl, a, c, b'⟩ := q
      rw [hp] at hr hP
      simp only [Bool.and_eq_true] at hP
      simp only at hr
      split_ifs at hr
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact hP.1.2
        · exact hP.2
      · simp at hr

end Cong

/-! ### `compReqsX` across coins, publics and widths -/

section Comp
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq F]
  {h n : ℕ} {hn : 0 < n} {nodes : Fin n → F} {b : Basis (Fin 3) F K} {δ : F}
  {orbit : StrictOrbitDomain F 3 h}

/-- **The compute request lists read only round-0 columns `< 69`, no coin, no public.** -/
theorem compReqsX_congr {chalV pubVal chalV' pubVal' : ℕ → F}
    (P : Fin (computeChipVCLHX hn nodes b δ chalV pubVal orbit).rap.w → F[X])
    (P' : Fin (computeChipVCLHX hn nodes b δ chalV' pubVal' orbit).rap.w → F[X])
    (hP : ∀ (j : ℕ) (h1 : j < (computeChipVCLHX hn nodes b δ chalV pubVal orbit).rap.w)
      (h2 : j < (computeChipVCLHX hn nodes b δ chalV' pubVal' orbit).rap.w), j < 69 → P ⟨j, h1⟩ = P' ⟨j, h2⟩)
    (bl : Bal) :
    (compReqsX (K := K) (hn := hn) (nodes := nodes) (chalV := chalV) (pubVal := pubVal) (orbit := orbit)
      (P := P) bl) =
    compReqsX (K := K) (hn := hn) (nodes := nodes) (chalV := chalV') (pubVal := pubVal') (orbit := orbit)
      (P := P') bl := by
  have hE : ∀ i, ∀ c < 69, (TeleC.envsN hn nodes chalV pubVal orbit P i).trace c =
      (TeleC.envsN hn nodes chalV' pubVal' orbit P' i).trace c := by
    intro i c hc
    simp only [TeleC.envsN, TeleC.rEF]
    split_ifs <;>
      exact DescentVSQ.envOfTrace_congrW 69 P P' (by rw [TraceJ8.widthC_eq]; omega)
        (by rw [TraceJ8.widthC_eq]; omega)
        (fun c h1 h2 hc => hP c h1 h2 hc) _ _ _ _ _ _ _ c hc
  unfold compReqsX
  refine congrArg List.flatten (List.map_congr_left fun i _ => ?_)
  rw [consQX_congr _ _ (hE i) bl]
  refine List.map_congr_left fun r hr => ?_
  exact keyX_congr 69 _ r (consQX_read _ bl r hr) _ _ (hE i)

end Comp

/-! ## 2. The other chips' IO lists read round-0 base columns only -/

section Chips
open Nock.Jet.RapJetJ8 (rowJ jRd jCons jProv)
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] (b : Basis (Fin 3) (ZMod p) K)
  {h h' n w w' : ℕ} (nodes : Fin n → ZMod p) (orbit : StrictOrbitDomain (ZMod p) 3 h)
  (orbit' : StrictOrbitDomain (ZMod p) 3 h') (chals pubs chals' pubs' : ℕ → K)
  (Q : Fin w → (ZMod p)[X]) (Q' : Fin w' → (ZMod p)[X])

/-- **A J row reads its columns `< 29` only** (and the public layout). -/
theorem rowJ_congr (lay : Fin n → Nock.Jet.ChipJ8.PRow) (hB : 29 ≤ w) (hB' : 29 ≤ w')
    (hQ : ∀ (c : ℕ) (h1 : c < w) (h2 : c < w'), c < 29 → Q ⟨c, h1⟩ = Q' ⟨c, h2⟩) :
    rowJ b nodes orbit chals pubs lay Q = rowJ b nodes orbit' chals' pubs' lay Q' := by
  funext i
  have he := DescentVSQ.envOfTrace_congrW 29 Q Q' hB hB' hQ orbit.ω orbit'.ω (nodes i)
    (Chips.ChipRAP.slotVal b 29 chals) (Chips.ChipRAP.slotVal b 29 pubs) (Chips.ChipRAP.slotVal b 29 chals') (Chips.ChipRAP.slotVal b 29 pubs')
  simp only [rowJ, Nock.Jet.RapJetJ8.jEF, he 18 (by norm_num), he 19 (by norm_num), he 20 (by norm_num),
    he 21 (by norm_num), he 22 (by norm_num), he 23 (by norm_num), he 24 (by norm_num), he 25 (by norm_num),
    he 26 (by norm_num), he 27 (by norm_num), he 28 (by norm_num)]

/-- **The J chip's three lists read its columns `< 29` only, no coin, no public.** -/
theorem jLists_congr (lay : Fin n → Nock.Jet.ChipJ8.PRow) (hB : 29 ≤ w) (hB' : 29 ≤ w')
    (hQ : ∀ (c : ℕ) (h1 : c < w) (h2 : c < w'), c < 29 → Q ⟨c, h1⟩ = Q' ⟨c, h2⟩) :
    jRd b nodes orbit chals pubs lay Q = jRd b nodes orbit' chals' pubs' lay Q' ∧
      jCons b nodes orbit chals pubs lay Q = jCons b nodes orbit' chals' pubs' lay Q' ∧
      jProv b nodes orbit chals pubs lay Q = jProv b nodes orbit' chals' pubs' lay Q' := by
  have hr := rowJ_congr b nodes orbit orbit' chals pubs chals' pubs' Q Q' lay hB hB' hQ
  refine ⟨?_, ?_, ?_⟩ <;> simp only [jRd, jCons, jProv, hr]

theorem keyHK_read : ∀ g ∈ (TwoProviderQ.keyHK : List (CoeffExpr (ZMod p))), rdOK 134 g = true := by
  simp [TwoProviderQ.keyHK, CellH.valE, Chips.ChipRAP.notE, rdOK, Chips.ChipRAP.cv]; decide

/-- **The cell table's wire providers read its columns `< 134` only.** -/
theorem cellProvsW_congr (hB : 134 ≤ w) (hB' : 134 ≤ w')
    (hQ : ∀ (c : ℕ) (h1 : c < w) (h2 : c < w'), c < 134 → Q ⟨c, h1⟩ = Q' ⟨c, h2⟩) :
    CellTwinKW.cellProvsW b nodes orbit chals pubs Q = CellTwinKW.cellProvsW b nodes orbit' chals' pubs' Q' := by
  unfold CellTwinKW.cellProvsW
  refine List.map_congr_left fun i _ => ?_
  have he := DescentVSQ.envOfTrace_congrW 134 Q Q' hB hB' hQ orbit.ω orbit'.ω (nodes i)
    (Chips.ChipRAP.slotVal b 134 chals) (Chips.ChipRAP.slotVal b 134 pubs) (Chips.ChipRAP.slotVal b 134 chals') (Chips.ChipRAP.slotVal b 134 pubs')
  rw [IOVS.keyVec5_congr 134 _ keyHK_read _ _ he, he CellH.mh (by decide)]

theorem incKey_read : ∀ g ∈ (AtomChipHQ.incKey : List (CoeffExpr (ZMod p))), rdOK 205 g = true := by
  simp [AtomChipHQ.incKey, Chips.ChipRAP.notE, rdOK, Chips.ChipRAP.cv]; decide

/-- **The atom table's inc providers read its columns `< 205` only.** -/
theorem atomIncProvs_congr (hB : 205 ≤ w) (hB' : 205 ≤ w')
    (hQ : ∀ (c : ℕ) (h1 : c < w) (h2 : c < w'), c < 205 → Q ⟨c, h1⟩ = Q' ⟨c, h2⟩) :
    ServiceJ8.atomIncProvs b nodes orbit chals pubs Q = ServiceJ8.atomIncProvs b nodes orbit' chals' pubs' Q' := by
  unfold ServiceJ8.atomIncProvs
  refine congrArg List.flatten (List.map_congr_left fun i _ => ?_)
  have he := DescentVSQ.envOfTrace_congrW 205 Q Q' hB hB' hQ orbit.ω orbit'.ω (nodes i)
    (Chips.ChipRAP.slotVal b 205 chals) (Chips.ChipRAP.slotVal b 205 pubs) (Chips.ChipRAP.slotVal b 205 chals') (Chips.ChipRAP.slotVal b 205 pubs')
  rw [IOVS.keyVec5_congr 205 _ incKey_read _ _ he, he AtomChipHQ.mi (by decide)]

end Chips

/-! ## 3. The per-row consume counts of the compute chip -/

section Count
open Nock.NockVMROM.Thm54.VclL.Handle.TeleCQX (act_zero prX_zero pr2X_zero)

/-- The per-row cap of each balance: `x` 3, `p` 2, `s` 2 (an `s5` row's `α` pair consumes two service records). -/
def capB : Bal → ℕ
  | .x => 3
  | .p => 2
  | .s => 2

/-- The number of records slot `S` can consume into `bl` on a row in state `j`. -/
def cntS (j : ℕ) (bl : Bal) (S : SlotX ℚ) : ℕ :=
  (S.ents.filter fun x => decide (x.bal = bl) && decide (j ∈ x.states)).length +
    (match S.pair with
     | some (_, _, _, b') => if b' = bl ∧ j ∈ S.pairStates then 2 else 0
     | none => 0)

theorem cnt_le (bl : Bal) : ∀ j < 17, ((ChipHX.slotsX : List (SlotX ℚ)).map (cntS j bl)).sum ≤ capB bl := by
  cases bl <;> decide

theorem filter_len_mono {α : Type} (l : List α) (p q : α → Bool) (h : ∀ x ∈ l, p x = true → q x = true) :
    (l.filter p).length ≤ (l.filter q).length := by
  induction l with
  | nil => simp
  | cons a t ih =>
    have ih' := ih fun x hx => h x (List.mem_cons_of_mem _ hx)
    have hq := h a List.mem_cons_self
    have hqt : (t.filter q).length ≤ (t.filter q).length + 1 := Nat.le_succ _
    cases hpa : p a <;> cases hqa : q a
    · simpa [List.filter_cons, hpa, hqa] using ih'
    · simpa [List.filter_cons, hpa, hqa] using ih'.trans hqt
    · simp [hpa, hqa] at hq
    · simpa [List.filter_cons, hpa, hqa] using ih'

variable {F : Type} [Field F] [DecidableEq F] {env : Env F} {j : ℕ}

theorem pair_flag (hB : BaseHoldsX env) (hOH : OneHotAt env j) {S : SlotX ℚ}
    (hS : S ∈ (ChipHX.slotsX : List (SlotX ℚ))) {fl : ℕ} {a c : List RE} {b' : Bal}
    (hp : S.pair = some (fl, a, c, b')) (hf : env.trace fl = 1) : j ∈ S.pairStates := by
  simp only [ChipHX.slotsX, List.mem_cons, List.not_mem_nil, or_false] at hS
  rcases hS with rfl | rfl | rfl | rfl
  · simp [slot0X] at hp
  · simp [slot1X] at hp
  · simp only [slot2X, Option.some.injEq, Prod.mk.injEq] at hp
    obtain ⟨rfl, -⟩ := hp
    by_contra hj
    have h5 : j ≠ 5 := fun h => hj (by simp [slot2X, h])
    have h12 : j ≠ 12 := fun h => hj (by simp [slot2X, h])
    rw [prX_zero hB hOH h5 h12] at hf; exact zero_ne_one hf
  · simp only [slot3X, Option.some.injEq, Prod.mk.injEq] at hp
    obtain ⟨rfl, -⟩ := hp
    by_contra hj
    have h5 : j ≠ 5 := fun h => hj (by simp [slot3X, h])
    rw [pr2X_zero hB hOH h5] at hf; exact zero_ne_one hf

theorem slot_count_le (hB : BaseHoldsX env) (hOH : OneHotAt env j) (bl : Bal) {S : SlotX ℚ}
    (hS : S ∈ (ChipHX.slotsX : List (SlotX ℚ))) :
    (((S.ents.filter fun x => decide (x.bal = bl)).filter fun x => decide (evalQX x.act env = 1)).map
      (·.rcd) ++ pairRecsB env bl S).length ≤ cntS j bl S := by
  rw [List.length_append, List.length_map, List.filter_filter]
  unfold cntS
  refine Nat.add_le_add ?_ ?_
  · refine filter_len_mono _ _ _ fun x hxS hx => ?_
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hx ⊢
    refine ⟨hx.2, ?_⟩
    by_contra hj
    rw [act_zero hB hOH hS hxS hj] at hx
    exact zero_ne_one hx.1
  · unfold pairRecsB
    cases hp : S.pair with
    | none => simp
    | some q =>
      obtain ⟨fl, a, c, b'⟩ := q
      simp only
      split_ifs with h1 h2
      · simp
      · exact absurd ⟨h1.1, pair_flag hB hOH hS hp h1.2⟩ h2
      · simp
      · simp

/-- **A row in state `j < 17` consumes at most `capB bl` records into `bl`.** -/
theorem consQX_length_le (hB : BaseHoldsX env) (hOH : OneHotAt env j) (hj : j < 17) (bl : Bal) :
    (consQX env bl).length ≤ capB bl := by
  unfold consQX
  rw [List.length_flatMap]
  refine le_trans ?_ (cnt_le bl j hj)
  exact List.sum_le_sum fun S hS => slot_count_le hB hOH bl hS

end Count

/-! ### The compute request counts -/

section CompCount
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq F]
  {h n : ℕ} {hn : 0 < n} {nodes : Fin n → F} {b : Basis (Fin 3) F K} {δ : F}
  {orbit : StrictOrbitDomain F 3 h} {chalV pubVal : ℕ → F}
  {P : Fin (computeChipVCLHX hn nodes b δ chalV pubVal orbit).rap.w → F[X]}

/-- **On an accepted compute trace, balance `bl` has at most `capB bl · n` compute requests.** -/
theorem compReqsX_length_le
    (hsat : RAP.SatisfiesWithPreprocessing (computeChipVCLHX hn nodes b δ chalV pubVal orbit) P)
    (hc : ChipHX.nStates < ringChar F) (bl : Bal) :
    (compReqsX (K := K) (hn := hn) (nodes := nodes) (chalV := chalV) (pubVal := pubVal) (orbit := orbit)
      (P := P) bl).length ≤ capB bl * n := by
  unfold compReqsX
  rw [List.length_flatMap]
  have hrow : ∀ i ∈ List.range n, ((consQX (TeleC.envsN hn nodes chalV pubVal orbit P i) bl).map
      fun r => (keyX (mOf bl) r (TeleC.envsN hn nodes chalV pubVal orbit P i) : Fin (mOf bl) → K)).length ≤
      capB bl := by
    intro i hi
    rw [List.length_map]
    have hB : BaseHoldsX (TeleC.envsN hn nodes chalV pubVal orbit P i) := by
      simp only [TeleC.envsN, TeleC.rEF]
      split_ifs <;> exact RapWalkJ8.baseX_of_sat hn nodes b δ _ _ orbit _ hsat _ (Chips.ChipRAP.mem_rowNodeSet _ _)
    exact consQX_length_le hB (RapWalkJ8.stX_spec hB hc) (RowDecodeVSX.stIdx_lt _) bl
  calc ((List.range n).map _).sum ≤ ((List.range n).map fun _ => capB bl).sum := List.sum_le_sum hrow
    _ = capB bl * n := by simp [mul_comm]

end CompCount

end

end Nock.NockVMROM.Thm54.VclL.Handle.ReadIOJ8
