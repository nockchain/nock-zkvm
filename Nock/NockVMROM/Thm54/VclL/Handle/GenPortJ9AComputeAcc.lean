/-
  Nock/NockVMROM/Thm54/VclL/Handle/GenPortJ9AComputeAcc.lean

-/
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9ACompute
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.TeleX9

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AComputeAcc

open Nock Nock.Field Nock.TraceGenExe Nock.V1J8 Nock.V1J8.Exe Nock.V1J8.Check Nock.V1J8.Gen

/-- `prefixSums` on a snoc: one more step. -/
theorem prefixSums_snoc (rows : List (Array (ZMod P))) (r : Array (ZMod P)) :
    prefixSums 18 (rows ++ [r]) =
      ((prefixSums 18 rows).1 ++ [(prefixSums 18 rows).2],
        Array.ofFn (n := 18) fun i => (prefixSums 18 rows).2.getD i 0 + r.getD i 0) := by
  unfold prefixSums
  rw [List.foldl_append]
  rfl

/-- **Total**: coordinate `i < 18` of the `prefixSums` total is the plain sum of the rows' coordinates. -/
theorem prefixSums_total_getD (rows : List (Array (ZMod P))) {i : ℕ} (hi : i < 18) :
    (prefixSums 18 rows).2.getD i 0 = ∑ j ∈ Finset.range rows.length, (rows.getD j #[]).getD i 0 := by
  induction rows using List.reverseRecOn with
  | nil =>
    simp [prefixSums, Array.getD_eq_getD_getElem?, hi]
  | append_singleton rows r ih =>
    rw [prefixSums_snoc]
    simp only [List.length_append, List.length_singleton, Finset.sum_range_succ]
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_ofFn]
    simp only [hi, dite_true, Option.getD_some]
    rw [ih]
    congr 1
    · apply Finset.sum_congr rfl
      intro x hx
      rw [Finset.mem_range] at hx
      rw [List.getD_append _ _ _ _ hx]
    · rw [List.getD_append_right _ _ _ _ (le_refl _)]
      simp

/-- The `.1` of `prefixSums` is the list of totals of the prefixes. -/
theorem prefixSums_fst (rows : List (Array (ZMod P))) :
    (prefixSums 18 rows).1 = (List.range rows.length).map fun j => (prefixSums 18 (rows.take j)).2 := by
  induction rows using List.reverseRecOn with
  | nil => simp [prefixSums]
  | append_singleton rows r ih =>
    rw [prefixSums_snoc, ih, List.length_append, List.length_singleton, List.range_succ, List.map_append]
    simp only [List.map_cons, List.map_nil, List.take_length]
    congr 1
    · apply List.map_congr_left
      intro j hj
      rw [List.mem_range] at hj
      rw [List.take_append_of_le_length hj.le]
    · rw [List.take_left]

/-- **Exclusive prefix sums**: for `j < |rows|` and `i < 18`, `accs[j][i] = Σ_{j' < j} rows[j'][i]`. -/
theorem prefixSums_getD (rows : List (Array (ZMod P))) {j : ℕ} (hj : j < rows.length) {i : ℕ} (hi : i < 18) :
    ((prefixSums 18 rows).1.getD j #[]).getD i 0 = ∑ j' ∈ Finset.range j, (rows.getD j' #[]).getD i 0 := by
  rw [prefixSums_fst]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hj, Option.map_some,
    Option.getD_some]
  rw [prefixSums_total_getD _ hi]
  have hl : (rows.take j).length = j := by simp; omega
  rw [hl]
  apply Finset.sum_congr rfl
  intro j' hj'
  rw [Finset.mem_range] at hj'
  simp [List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hj']

/-! ## The per-row term: `termVal` coordinate = `termRow9` entry -/

open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.VclL.Handle Nock.Reified
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHX (slotsX Bal)
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHX9 (slotsX9)
open Nock.V1J8.Gen

/-- **Per-row term, generic in the basis**: at a stage-2 environment `E` whose slot activities agree with the
executable's (`hAct`) and whose inverse columns carry the executable's limbs (`hInv`), coordinate `k < 3` of
`termVal` over the cast twin slots is the executable `foldl` of `termRow9`. -/
theorem cNA_termVal {K : Type} [Field K] [Algebra (ZMod P) K] [FiniteDimensional (ZMod P) K] [Fintype K] (b : Module.Basis (Fin 3) (ZMod P) K)
    (bl : Bal) (im : Bool) (E : Env (ZMod P)) (iv : Array K6) (e : Env (ZMod P))
    (hAct : (slotsX9 (F := ℚ)).map (fun S => ChipHX.evalQX (S.actB bl) E) =
      (slotsX9 (F := ZMod P)).map fun S => (S.actB bl).eval e)
    (hInv : ∀ s, s < 4 → ∀ k, k < 3 →
      E.trace (69 + 6 * s + k) = limbZ (iv.getD s 0).re k ∧ E.trace (72 + 6 * s + k) = limbZ (iv.getD s 0).im k)
    {k : ℕ} (hk : k < 3) :
    Nock.NockVMROM.Thm54.VclL.HonestTraceX.cNA b
        (Nock.NockVMROM.Thm54.VclL.Compute.LogUp.termVal b
          (Nock.NockVMROM.Thm54.VclL.HonestTraceX9.slotsF9 bl im) E) k =
      (((slotsX9 (F := ZMod P)).map fun S => (S.actB bl).eval e).zipIdx 0).foldl
        (fun s (x : ZMod P × ℕ) => s + x.1 * limbZ (if im then (iv.getD x.2 0).im else (iv.getD x.2 0).re) k) 0 := by
  rw [show Nock.NockVMROM.Thm54.VclL.HonestTraceX.cNA b _ k = _ from
    Nock.NockVMROM.Thm54.VclL.HonestTraceX.cNA_coord b _ ⟨k, hk⟩]
  have hT : Nock.NockVMROM.Thm54.VclL.Compute.LogUp.termVal b
        (Nock.NockVMROM.Thm54.VclL.HonestTraceX9.slotsF9 bl im) E =
      Nock.NockVMROM.Thm54.VclL.Handle.TeleCQX.termValX b
        (Nock.NockVMROM.Thm54.VclL.Handle.TeleX9.slotsB9 bl im) E := by
    simp only [Nock.NockVMROM.Thm54.VclL.Compute.LogUp.termVal, Nock.NockVMROM.Thm54.VclL.Handle.TeleCQX.termValX,
      Nock.NockVMROM.Thm54.VclL.HonestTraceX9.slotsF9, Nock.NockVMROM.Thm54.VclL.HonestTraceX9.slotsQ9,
      Nock.NockVMROM.Thm54.VclL.Handle.TeleX9.slotsB9, List.map_map, Function.comp_def,
      Nock.NockVMROM.Thm54.VclL.Handle.castSlot, Nock.NockVMROM.Thm54.VclL.HonestTraceX.eval_mapC_castX]
  rw [hT, Nock.NockVMROM.Thm54.VclL.Handle.TeleCQX.coord_termValX,
    Nock.NockVMROM.Thm54.VclL.Handle.TeleCQX.evalQX_termCoord]
  simp only [Nock.NockVMROM.Thm54.VclL.Handle.TeleX9.slotsB9, Nock.NockVMROM.Thm54.VclL.Handle.ChipHX9.slotsX9,
    List.map_cons, List.map_nil, List.map_map, Function.comp_def] at hAct ⊢
  simp only [List.cons.injEq, and_true] at hAct
  obtain ⟨h0, h1, h2, h3⟩ := hAct
  have e0 : (Nock.NockVMROM.Thm54.VclL.Handle.ChipHX9.slot0X9 (F := ℚ)).inv = 69 := rfl
  have e1 : (Nock.NockVMROM.Thm54.VclL.Handle.ChipHX9.slot1X9 (F := ℚ)).inv = 75 := rfl
  have e2 : (Nock.NockVMROM.Thm54.VclL.Handle.ChipHX9.slot2X9 (F := ℚ)).inv = 81 := rfl
  have e3 : (Nock.NockVMROM.Thm54.VclL.Handle.ChipHX9.slot3X9 (F := ℚ)).inv = 87 := rfl
  have f0 : (Nock.NockVMROM.Thm54.VclL.Handle.ChipHX9.slot0X9 (F := ℚ)).invIm = 72 := rfl
  have f1 : (Nock.NockVMROM.Thm54.VclL.Handle.ChipHX9.slot1X9 (F := ℚ)).invIm = 78 := rfl
  have f2 : (Nock.NockVMROM.Thm54.VclL.Handle.ChipHX9.slot2X9 (F := ℚ)).invIm = 84 := rfl
  have f3 : (Nock.NockVMROM.Thm54.VclL.Handle.ChipHX9.slot3X9 (F := ℚ)).invIm = 90 := rfl
  have g0 := hInv 0 (by omega) k hk
  have g1 := hInv 1 (by omega) k hk
  have g2 := hInv 2 (by omega) k hk
  have g3 := hInv 3 (by omega) k hk
  norm_num [Array.getD_eq_getD_getElem?] at g0 g1 g2 g3
  cases im <;>
  simp [List.zipIdx_cons, List.foldl_cons, e0, e1, e2, e3, f0, f1, f2, f3, h0, h1, h2, h3, g0, g1, g2, g3] <;>
  ring

/-- `cNA` is additive over finite sums. -/
theorem cNA_sum {K : Type} [Field K] [Algebra (ZMod P) K] [FiniteDimensional (ZMod P) K] [Fintype K]
    (b : Module.Basis (Fin 3) (ZMod P) K) {ι : Type} (s : Finset ι) (f : ι → K) (k : ℕ) :
    Nock.NockVMROM.Thm54.VclL.HonestTraceX.cNA b (∑ i ∈ s, f i) k =
      ∑ i ∈ s, Nock.NockVMROM.Thm54.VclL.HonestTraceX.cNA b (f i) k := by
  classical
  unfold Nock.NockVMROM.Thm54.VclL.HonestTraceX.cNA
  split_ifs with h
  · simp [Nock.NockVMROM.Thm54.CoordinateBasis.coord, map_sum, Finsupp.finsetSum_apply]
  · simp

open Nock.Edit Nock.Edit.GenX Nock.Walk
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AGen (LX9)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ACompRow (invPermX9)
open Nock.V1J9A.GenCompX9
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9ACompute

/-- **Accumulator columns (twin 93..110) of `compTable9` = `trX9`**, modulo the two per-row facts that the
stage-2 environment `env1` agrees with the executable environment `envX9` (`hAct`: slot activities, `hInv`: the
inverse columns carry the executable's limbs).  Basis-generic. -/
theorem compTable9_eq_trX9_acc {K : Type} [Field K] [Algebra (ZMod P) K] [FiniteDimensional (ZMod P) K]
    [Fintype K] (b : Module.Basis (Fin 3) (ZMod P) K) (δ : ZMod P)
    [Fact (¬ IsSquare (algebraMap (ZMod P) K δ))]
    (H : Noun → ℕ × ℕ) (pd : RowNX → ℕ × (ℕ × ℕ) × (ℕ × ℕ)) (idOf : ℕ → ℕ)
    (W : List (NTree LX9)) (pub : ℕ → ZMod P) (χe : CoinsE) (chalV pubVal : ℕ → ZMod P) (ln cnt acc : ℕ → K)
    (hAct : ∀ j', j' < W.length → ∀ bl,
      (slotsX9 (F := ℚ)).map (fun S => ChipHX.evalQX (S.actB bl)
          (Nock.NockVMROM.Thm54.VclL.HonestTraceX9.env1 b δ H pd idOf W chalV pubVal j')) =
        (slotsX9 (F := ZMod P)).map fun S => (S.actB bl).eval (envX9 H pd idOf W pub χe j'))
    (hInv : ∀ j', j' < W.length → ∀ s, s < 4 → ∀ k, k < 3 →
      (Nock.NockVMROM.Thm54.VclL.HonestTraceX9.env1 b δ H pd idOf W chalV pubVal j').trace (69 + 6 * s + k) =
          limbZ ((invsOf9 (envX9 H pd idOf W pub χe j')).getD s 0).re k ∧
      (Nock.NockVMROM.Thm54.VclL.HonestTraceX9.env1 b δ H pd idOf W chalV pubVal j').trace (72 + 6 * s + k) =
          limbZ ((invsOf9 (envX9 H pd idOf W pub χe j')).getD s 0).im k)
    {j : ℕ} (hj : j < W.length) {d : ℕ} (hd : d < 137)
    (hr : 93 ≤ invPermX9 d ∧ invPermX9 d < 111) :
    ((compTable9 H pd idOf W pub χe).getD j #[]).getD d 0 =
      Nock.NockVMROM.Thm54.VclL.HonestTraceX9.trX9 b δ H pd idOf W chalV pubVal ln cnt acc j (invPermX9 d) := by
  rw [compTable9_getD H pd idOf W pub χe hj hd]
  unfold Nock.NockVMROM.Thm54.VclL.HonestTraceX9.trX9
  generalize hc : invPermX9 d = c at hr ⊢
  obtain ⟨h1, h2⟩ := hr
  simp only [compColD9, if_neg (show ¬ (c < 69 ∨ 123 ≤ c) by omega), if_neg (show ¬ c < 93 by omega),
    if_pos h2, show ¬ c < 69 by omega]
  simp only [Nock.NockVMROM.Thm54.VclL.HonestTraceX9.accV9]
  rw [cNA_sum]
  have hlen : ((List.range W.length).map fun j => envX9 H pd idOf W pub χe j).length = W.length := by simp
  rw [if_neg (by rintro (h | h) <;> first | exact h | omega)]
  rw [prefixSums_getD _ (by simp; omega) (show c - 93 < 18 by omega)]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : i < W.length := lt_trans (Finset.mem_range.1 hi) hj
  have hrow : ((List.map (fun x => termRow9 x.1 x.2)
      ((List.map (fun j => envX9 H pd idOf W pub χe j) (List.range W.length)).zip
        (List.map invsOf9 (List.map (fun j => envX9 H pd idOf W pub χe j) (List.range W.length))))).getD i #[]) =
      termRow9 (envX9 H pd idOf W pub χe i) (invsOf9 (envX9 H pd idOf W pub χe i)) := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_zip_eq_some, hi']
  rw [hrow]
  have hs : c - 93 < 18 := by omega
  have ha : (c - 93) / 3 < 6 := by omega
  have hent : (termRow9 (envX9 H pd idOf W pub χe i) (invsOf9 (envX9 H pd idOf W pub χe i))).getD (c - 93) 0 =
      (((slotsX9 (F := ZMod P)).map fun S =>
          (S.actB (accSpecE ((c - 93) / 3)).1).eval (envX9 H pd idOf W pub χe i)).zipIdx 0).foldl
        (fun s (x : ZMod P × ℕ) => s + x.1 * limbZ (if (accSpecE ((c - 93) / 3)).2
          then ((invsOf9 (envX9 H pd idOf W pub χe i)).getD x.2 0).im
          else ((invsOf9 (envX9 H pd idOf W pub χe i)).getD x.2 0).re) ((c - 93) % 3)) 0 := by
    simp only [termRow9, Array.getD_eq_getD_getElem?, Array.getElem?_ofFn, hs, dite_true, Option.getD_some, actsOf9]
  rw [hent]
  have hspec : Nock.NockVMROM.Thm54.VclL.HonestTraceX.accSpec ((c - 93) / 3) = accSpecE ((c - 93) / 3) := by
    generalize (c - 93) / 3 = a at ha
    interval_cases a <;> rfl
  rw [hspec]
  exact (cNA_termVal b _ _ _ _ _ (hAct i hi' _) (hInv i hi') (Nat.mod_lt _ (by norm_num))).symm

/-- The stage-1 environments agree: `env0` at the executable coins is `envX9`. -/
theorem env0_eq_envX9 (H : Noun → ℕ × ℕ) (pd : RowNX → ℕ × (ℕ × ℕ) × (ℕ × ℕ)) (idOf : ℕ → ℕ)
    (W : List (NTree LX9)) (pub : ℕ → ZMod P) (χe : CoinsE) (j : ℕ) :
    Nock.NockVMROM.Thm54.VclL.HonestTraceX9.env0 H pd idOf W (Example.chalE χe) pub j =
      envX9 H pd idOf W pub χe j := by
  haveI : CharP (ZMod P) P := ZMod.charP P
  have h : ∀ j', Nock.NockVMROM.Thm54.VclL.HonestTraceX9.baseT9 H pd idOf W j' = baseFn9 H pd idOf W j' := by
    intro j'
    funext c
    unfold Nock.NockVMROM.Thm54.VclL.HonestTraceX9.baseT9 baseFn9
    rw [Nock.V1J9A.FillX9.colX9E_eq]
  unfold Nock.NockVMROM.Thm54.VclL.HonestTraceX9.env0 envX9
  rw [h, h]

/-- **`hInv` discharged** at the concrete parameters. -/
theorem hInv_conc (H : Noun → ℕ × ℕ) (pd : RowNX → ℕ × (ℕ × ℕ) × (ℕ × ℕ)) (idOf : ℕ → ℕ)
    (W : List (NTree LX9)) (pub : ℕ → ZMod P) (χe : CoinsE) (j : ℕ) {s : ℕ} (hs : s < 4) {k : ℕ} (hk : k < 3) :
    (Nock.NockVMROM.Thm54.VclL.HonestTraceX9.env1 powerBasis3 deltaF H pd idOf W (Example.chalE χe) pub j).trace
        (69 + 6 * s + k) = limbZ ((invsOf9 (envX9 H pd idOf W pub χe j)).getD s 0).re k ∧
    (Nock.NockVMROM.Thm54.VclL.HonestTraceX9.env1 powerBasis3 deltaF H pd idOf W (Example.chalE χe) pub j).trace
        (72 + 6 * s + k) = limbZ ((invsOf9 (envX9 H pd idOf W pub χe j)).getD s 0).im k := by
  have hiv : (invsOf9 (envX9 H pd idOf W pub χe j)).getD s 0 = invE9 (envX9 H pd idOf W pub χe j) s := by
    simp [invsOf9, Array.getD_eq_getD_getElem?, hs]
  have hV : Nock.NockVMROM.Thm54.VclL.HonestTraceX9.invV9 powerBasis3 deltaF H pd idOf W (Example.chalE χe) pub j
      (Nock.NockVMROM.Thm54.VclL.HonestTraceX9.slotAt9 s) = K6.toQ (invE9 (envX9 H pd idOf W pub χe j) s) := by
    unfold Nock.NockVMROM.Thm54.VclL.HonestTraceX9.invV9
    rw [env0_eq_envX9]
    exact (toQ_invE9 _ s).symm
  have e1 : Nock.NockVMROM.Thm54.T0Tower.Quad.re _ (K6.toQ (invE9 (envX9 H pd idOf W pub χe j) s)) =
      K3.toK (invE9 (envX9 H pd idOf W pub χe j) s).re := by
    unfold K6.toQ; exact Nock.NockVMROM.Thm54.T0Tower.Quad.re_mk _ _ _
  have e2 : Nock.NockVMROM.Thm54.T0Tower.Quad.im _ (K6.toQ (invE9 (envX9 H pd idOf W pub χe j) s)) =
      K3.toK (invE9 (envX9 H pd idOf W pub χe j) s).im := by
    unfold K6.toQ; exact Nock.NockVMROM.Thm54.T0Tower.Quad.im_mk _ _ _
  constructor
  · unfold Nock.NockVMROM.Thm54.VclL.HonestTraceX9.env1
    dsimp only
    unfold Nock.NockVMROM.Thm54.VclL.HonestTraceX9.preT9 Nock.NockVMROM.Thm54.VclL.HonestTraceX9.invCol9
    rw [if_neg (by omega), if_pos (by omega), if_pos (by omega)]
    have h1 : (69 + 6 * s + k - 69) / 6 = s := by omega
    have h2 : (69 + 6 * s + k - 69) % 6 = k := by omega
    rw [h1, h2, hV, hiv, e1]
    unfold Nock.NockVMROM.Thm54.VclL.HonestTraceX.cNA
    rw [dif_pos hk]
    exact coord_K _ k hk
  · unfold Nock.NockVMROM.Thm54.VclL.HonestTraceX9.env1
    dsimp only
    unfold Nock.NockVMROM.Thm54.VclL.HonestTraceX9.preT9 Nock.NockVMROM.Thm54.VclL.HonestTraceX9.invCol9
    rw [if_neg (by omega), if_pos (by omega), if_neg (by omega)]
    have h1 : (72 + 6 * s + k - 69) / 6 = s := by omega
    have h2 : (72 + 6 * s + k - 69) % 6 - 3 = k := by omega
    rw [h1, h2, hV, hiv, e2]
    unfold Nock.NockVMROM.Thm54.VclL.HonestTraceX.cNA
    rw [dif_pos hk]
    exact coord_K _ k hk

theorem castSlotX_actB_eval (S : ChipHX.SlotX ℚ) (bl : Bal) (e : Env (ZMod P)) :
    ((TeleCQX.castSlotX (F := ZMod P) S).actB bl).eval e = ChipHX.evalQX (S.actB bl) e := by
  rw [TeleCQX.evalQX_actB]
  unfold ChipHX.SlotX.actB
  have hb : ∀ x : ChipHX.EntX ℚ, (TeleCQX.castEntX (F := ZMod P) x).bal = x.bal := fun _ => rfl
  simp only [TeleCQX.castSlotX, List.filter_map, Function.comp_def, hb]
  show _ + _ = _
  have h1 := TeleCQX.castEntX_sumAct (F := ZMod P)
    (S.ents.filter fun x => decide (x.bal = bl)) e
  rw [h1]
  congr 1
  rcases hp : S.pair with _ | ⟨fl, a, b, b'⟩
  · rfl
  · by_cases h : b' = bl <;> simp [h, TeleCQX.pairFX, hp, ChipH.cc] <;> rfl

/-- **`hAct` discharged** at the concrete parameters: slot activities read only round-0 columns `< 69`. -/
theorem hAct_conc (H : Noun → ℕ × ℕ) (pd : RowNX → ℕ × (ℕ × ℕ) × (ℕ × ℕ)) (idOf : ℕ → ℕ)
    (W : List (NTree LX9)) (pub : ℕ → ZMod P) (χe : CoinsE) (j : ℕ) (bl : Bal) :
    (slotsX9 (F := ℚ)).map (fun S => ChipHX.evalQX (S.actB bl)
        (Nock.NockVMROM.Thm54.VclL.HonestTraceX9.env1 powerBasis3 deltaF H pd idOf W (Example.chalE χe) pub j)) =
      (slotsX9 (F := ZMod P)).map fun S => (S.actB bl).eval (envX9 H pd idOf W pub χe j) := by
  rw [← Nock.NockVMROM.Thm54.VclL.Handle.TeleX9.slotsX9_cast (F := ZMod P), List.map_map]
  refine List.map_congr_left fun S hS => ?_
  simp only [Function.comp_def]
  rw [castSlotX_actB_eval, ← env0_eq_envX9 H pd idOf W pub χe j]
  have hf := List.all_eq_true.mp Nock.NockVMROM.Thm54.VclL.HonestTraceX9.slotsAct_ok9 S hS
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hf
  obtain ⟨⟨⟨⟨hx, hp⟩, hs'⟩, hi⟩, hii⟩ := hf
  have hact : Nock.NockVMROM.Thm54.VclL.HonestTraceX.okC Nock.NockVMROM.Thm54.VclL.HonestTraceX9.okFs9 (S.actB bl) = true := by
    cases bl <;> assumption
  rw [← Nock.NockVMROM.Thm54.VclL.HonestTraceX.eval_mapC_castX, ← Nock.NockVMROM.Thm54.VclL.HonestTraceX.eval_mapC_castX]
  refine Nock.NockVMROM.Thm54.VclL.HonestTraceX.eval_okC Nock.NockVMROM.Thm54.VclL.HonestTraceX9.okFs9 _
    (by rw [Nock.NockVMROM.Thm54.VclL.HonestTraceX.okC_mapC]; exact hact) _ _ fun k i hk => ?_
  cases k <;> simp only [Nock.NockVMROM.Thm54.VclL.HonestTraceX9.okFs9, Bool.false_eq_true] at hk
  rw [Nock.NockVMROM.Thm54.VclL.HonestTraceX9.r0_iff] at hk
  show (Nock.NockVMROM.Thm54.VclL.HonestTraceX9.env1 powerBasis3 deltaF H pd idOf W (Example.chalE χe) pub j).trace i =
    (Nock.NockVMROM.Thm54.VclL.HonestTraceX9.env0 H pd idOf W (Example.chalE χe) pub j).trace i
  unfold Nock.NockVMROM.Thm54.VclL.HonestTraceX9.env1 Nock.NockVMROM.Thm54.VclL.HonestTraceX9.env0
    Nock.NockVMROM.Thm54.VclL.HonestTraceX9.preT9
  dsimp only
  rcases hk with h69 | ⟨h1, h2⟩
  · rw [if_pos h69]
  · rw [if_neg (by omega), if_neg (by omega), if_pos ⟨h1, h2⟩]

/-- **Accumulator columns, unconditional** at `b = powerBasis3`, `δ = deltaF`, `K = KC`. -/
theorem compTable9_eq_trX9_acc_conc (H : Noun → ℕ × ℕ) (pd : RowNX → ℕ × (ℕ × ℕ) × (ℕ × ℕ)) (idOf : ℕ → ℕ)
    (W : List (NTree LX9)) (pub : ℕ → ZMod P) (χe : CoinsE) (ln cnt acc : ℕ → KC)
    {j : ℕ} (hj : j < W.length) {d : ℕ} (hd : d < 137)
    (hr : 93 ≤ invPermX9 d ∧ invPermX9 d < 111) :
    ((compTable9 H pd idOf W pub χe).getD j #[]).getD d 0 =
      Nock.NockVMROM.Thm54.VclL.HonestTraceX9.trX9 powerBasis3 deltaF H pd idOf W (Example.chalE χe) pub ln cnt acc
        j (invPermX9 d) :=
  compTable9_eq_trX9_acc powerBasis3 deltaF H pd idOf W pub χe (Example.chalE χe) pub ln cnt acc
    (fun j' _ bl => hAct_conc H pd idOf W pub χe j' bl)
    (fun j' _ s hs k hk => hInv_conc H pd idOf W pub χe j' hs hk) hj hd hr

end Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AComputeAcc

#print axioms Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AComputeAcc.hAct_conc
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AComputeAcc.compTable9_eq_trX9_acc_conc

#print axioms Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AComputeAcc.compTable9_eq_trX9_acc
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AComputeAcc.cNA_termVal
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AComputeAcc.cNA_sum
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AComputeAcc.env0_eq_envX9
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AComputeAcc.hInv_conc

#print axioms Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AComputeAcc.prefixSums_getD
