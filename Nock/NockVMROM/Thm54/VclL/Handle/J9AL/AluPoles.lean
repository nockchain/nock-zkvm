/-
  Nock/NockVMROM/Thm54/VclL/Handle/J9AL/AluPoles.lean

  **The ALU-pole bad family** (the twin of the
  J-9 A pole families `famAX` / `famSP` / `famCellV`).

  The ALU's five LogUp denominators at row `i` of an honest table `T y` (the table built at the limb coin
  `y = (χ₁₇, χ₁₈)`), at the coins `chalsALJ8`:
  * `dV` (validity, `den valKey`) `= ρV + RLC_{γV}(valKey row)` with `ρV = (χ₅, χ₇)`, `γV = (χ₄, χ₆)`
    (`den_ev_compress'`, `chalsALJ8_ok`); the pole-free part reads `χ₂ χ₃` (the seed `z`, leaves `37 / 38`),
    `χ₄ χ₆` and `y`, never `χ₅`: one pin event on `χ₅`;
  * `dR dO dJ dX` (`denKeyQ` of the four service / export keys) `= ρH + RLC_{γH}(key row)` with
    `ρH = (χ₁₂, χ₁₆)`, `γH = (χ₁₁, χ₁₅)` (`denKeyQ_evL`, leaves `33..36`, `chals_pair`); the pole-free part reads
    `γH` and `y`, never `χ₁₂`: one pin event on `χ₁₂` each.

  `famAL δ T N`: `5 N` pin events (cost `1` each, `costL = 5 N`); outside them every one of the five denominators
  is non-zero at EVERY row `i < N` (`famAL_good`), which gives the `hden` hypothesis of the stage 1–3 theorem
  (`hden_of_famAL`) with no activity condition.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.J9AL.AluSatRows
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.ComplJ9AChipsOK

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Nock.NockVMROM.Thm54.VclL.Handle.AluPoles

open Nock Nock.Reified
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.T0Tower Nock.NockVMROM.Thm54.SVFrame
open Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Bad
open Nock.NockVMROM.Thm54.VclL.Handle.BalanceQ (liftRec)
open Nock.NockVMROM.Thm54.VclL.Handle.AluHonestRows (BRow QRow kvec)
open Nock.NockVMROM.Thm54.VclL.Handle.AluSatRows
open Nock.NockVMROM.Thm54.VclL.Handle.AluSZChipJ9 (chalsALJ8 chalsALJ8_ok chalsALJ8_zAt chalsALJ8_agree valKey
  keyRgE opRecE keyJetE keyXE)

noncomputable section

section Poles
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

/-- The limb coin `y = (χ₁₇, χ₁₈)`. -/
def yOf (χ : Coins frameJ8 K) : Quad (algebraMap (ZMod p) K δ) := Quad.mk _ (χ cY1) (χ cY2)

/-- The four service / export keys of the ALU. -/
def hKeys : List (List (CoeffExpr (ZMod p))) := [keyRgE, opRecE, keyJetE, keyXE]

theorem hKeys_len : ∀ l ∈ (hKeys : List (List (CoeffExpr (ZMod p)))), l.length ≤ 8 := by
  intro l hl
  simp only [hKeys, List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl | rfl | rfl <;>
    simp [keyRgE, opRecE, keyJetE, keyXE, AluSZChipJ9.keyRgRE, AluSZChipJ9.opRecRE, AluSZChipJ9.keyJetRE,
      AluSZChipJ9.keyXRE]

/-- The validity key vector of row `i` depends on the coins only through leaves `37 / 38`. -/
theorem keyVec_valKey_congr (kv nx pb : ℕ → K) (c c' : ℕ → K) (eF : Env (ZMod p))
    (h37 : c 37 = c' 37) (h38 : c 38 = c' 38) :
    keyVec δ 5 (valKey : List (QE (ZMod p))) ⟨kv, nx, c, pb⟩ eF =
      keyVec δ 5 (valKey : List (QE (ZMod p))) ⟨kv, nx, c', pb⟩ eF := by
  funext k
  fin_cases k <;>
    simp [keyVec, valKey, Nock.NockVMROM.Thm54.VclL.Handle.AtomChipHQ.zAt, ev_chal, ev_zero, ev_var, ev_base,
      h37, h38]

theorem chalsALJ8_37 (χ : Coins frameJ8 K) : chalsALJ8 δ χ 37 = χ WeightsJ8.c2 := by
  have := congrArg (Quad.re _) (chalsALJ8_zAt δ χ)
  simpa only [Quad.re_mk] using this

theorem chalsALJ8_38 (χ : Coins frameJ8 K) : chalsALJ8 δ χ 38 = χ WeightsJ8.c3 := by
  have := congrArg (Quad.im _) (chalsALJ8_zAt δ χ)
  simpa only [Quad.im_mk] using this

variable (T : Quad (algebraMap (ZMod p) K δ) → List (BRow (ZMod p) × QRow (Quad (algebraMap (ZMod p) K δ))))

/-- The pole-free part of row `i`'s validity denominator. -/
def xV (i : ℕ) (χ : Coins frameJ8 K) : 𝕂′ :=
  FiniteIO.compress (m := 5) ⟨Quad.mk _ (χ WeightsJ8.c4) (χ WeightsJ8.c6), 0⟩
    (keyVec δ 5 (valKey : List (QE (ZMod p))) (eKM δ (chalsALJ8 δ χ) (T (yOf δ χ)) i) (eFM δ (T (yOf δ χ)) i))

/-- The pole-free part of row `i`'s denominator of key `l`. -/
def xH (l : List (CoeffExpr (ZMod p))) (i : ℕ) (χ : Coins frameJ8 K) : 𝕂′ :=
  FiniteIO.compress (⟨γH δ χ, 0⟩ : FiniteIO.IOCoins 𝕂′)
    (liftRec (K := K) (L := 𝕂′) (AxisChipJ9.keyVecL (K := K) 8 l (eFM δ (T (yOf δ χ)) i)))

/-- **The ALU pole family**: per row `i < N`, one pin on `χ₅` (validity) and four pins on `χ₁₂` (service,
export). -/
def famAL (N : ℕ) : List (BadSpec K) :=
  (List.range N).flatMap fun i =>
    quadPole δ WeightsJ8.c5 (xV δ T i) :: hKeys.map fun l => quadPole δ InhabJ8Good.c12 (xH δ T l i)

theorem yOf_off (i : Fin frameJ8.n) (hi1 : i ≠ cY1) (hi2 : i ≠ cY2) (χ χ' : Coins frameJ8 K)
    (h : ∀ k, k ≠ i → χ k = χ' k) : yOf δ χ = yOf δ χ' := by
  simp only [yOf, h cY1 (Ne.symm hi1), h cY2 (Ne.symm hi2)]

theorem xV_readsOff (i : ℕ) : ReadsOff WeightsJ8.c5 (xV δ T i) := by
  intro χ χ' h
  have hy := yOf_off δ WeightsJ8.c5 (by decide) (by decide) χ χ' h
  have h37 : chalsALJ8 δ χ 37 = chalsALJ8 δ χ' 37 := by
    rw [chalsALJ8_37, chalsALJ8_37, h WeightsJ8.c2 (by decide)]
  have h38 : chalsALJ8 δ χ 38 = chalsALJ8 δ χ' 38 := by
    rw [chalsALJ8_38, chalsALJ8_38, h WeightsJ8.c3 (by decide)]
  simp only [xV, eKM, hy, h WeightsJ8.c4 (by decide), h WeightsJ8.c6 (by decide)]
  rw [keyVec_valKey_congr δ _ _ _ _ _ _ h37 h38]

theorem xH_readsOff (l : List (CoeffExpr (ZMod p))) (i : ℕ) : ReadsOff InhabJ8Good.c12 (xH δ T l i) := by
  intro χ χ' h
  have hy := yOf_off δ InhabJ8Good.c12 (by decide) (by decide) χ χ' h
  simp only [xH, hy, γH_readsOff δ χ χ' h]

theorem famAL_OK (N : ℕ) : ∀ e ∈ famAL δ T N, e.OK := by
  intro e he
  obtain ⟨i, -, he⟩ := List.mem_flatMap.mp he
  rcases List.mem_cons.mp he with rfl | he
  · exact quadPole_OK δ _ _ (xV_readsOff δ T i)
  · obtain ⟨l, -, rfl⟩ := List.mem_map.mp he
    exact quadPole_OK δ _ _ (xH_readsOff δ T l i)

theorem famAL_length (N : ℕ) : (famAL δ T N).length = 5 * N := by
  simp [famAL, hKeys, List.length_flatMap, Function.comp_def]
  omega

theorem famAL_cost (N : ℕ) : costL (famAL δ T N) = 5 * N := by
  have h : ∀ s ∈ famAL δ T N, s.cost = 1 := by
    intro s hs
    obtain ⟨i, -, he⟩ := List.mem_flatMap.mp hs
    rcases List.mem_cons.mp he with rfl | he
    · rfl
    · obtain ⟨l, -, rfl⟩ := List.mem_map.mp he
      rfl
  rw [costL, List.map_congr_left h, List.map_const', List.sum_replicate, famAL_length]
  simp

/-- The handle coins at `chalsALJ8`'s leaves `33 .. 36`. -/
theorem coinsQ_AL (χ : Coins frameJ8 K) (tb : List (BRow (ZMod p) × QRow 𝕂′)) (i : ℕ) :
    TeleHQ.coinsQ δ (eKM δ (chalsALJ8 δ χ) tb i) = (⟨γH δ χ, ρH δ χ⟩ : FiniteIO.IOCoins 𝕂′) := by
  obtain ⟨h1, h2⟩ := ComplJ9AChipsOK.chals_pair δ χ
  show (⟨Quad.mk _ (chalsALJ8 δ χ 33) (chalsALJ8 δ χ 35), Quad.mk _ (chalsALJ8 δ χ 34) (chalsALJ8 δ χ 36)⟩ :
    FiniteIO.IOCoins 𝕂′) = _
  rw [chalsALJ8_agree δ χ 33 (by norm_num) (by norm_num), chalsALJ8_agree δ χ 34 (by norm_num) (by norm_num),
    chalsALJ8_agree δ χ 35 (by norm_num) (by norm_num), chalsALJ8_agree δ χ 36 (by norm_num) (by norm_num), h1, h2]

/-- **Outside the ALU pole family every ALU denominator is non-zero at every row `i < N`.** -/
theorem famAL_good (N : ℕ) (χ : Coins frameJ8 K) (hχ : ∀ e ∈ famAL δ T N, χ ∉ e.ev) (i : ℕ) (hi : i < N) :
    dV δ (chalsALJ8 δ χ) (T (yOf δ χ)) i ≠ 0 ∧ dR δ (chalsALJ8 δ χ) (T (yOf δ χ)) i ≠ 0 ∧
      dO δ (chalsALJ8 δ χ) (T (yOf δ χ)) i ≠ 0 ∧ dJ δ (chalsALJ8 δ χ) (T (yOf δ χ)) i ≠ 0 ∧
      dX δ (chalsALJ8 δ χ) (T (yOf δ χ)) i ≠ 0 := by
  have hmem : ∀ e, e ∈ (quadPole δ WeightsJ8.c5 (xV δ T i) ::
      hKeys.map fun l => quadPole δ InhabJ8Good.c12 (xH δ T l i)) → χ ∉ e.ev :=
    fun e he => hχ e (List.mem_flatMap.mpr ⟨i, List.mem_range.mpr hi, he⟩)
  -- validity
  have hV : dV δ (chalsALJ8 δ χ) (T (yOf δ χ)) i ≠ 0 := by
    have hok := chalsOK_mono δ (show 5 ≤ 11 by norm_num) (chalsALJ8_ok δ χ)
    have e := den_ev_compress' δ (valKey : List (QE (ZMod p))) (m := 5) rfl
      (eKM δ (chalsALJ8 δ χ) (T (yOf δ χ)) i) (eFM δ (T (yOf δ χ)) i) _ _ hok
    show (den δ valKey).ev δ (eKM δ (chalsALJ8 δ χ) (T (yOf δ χ)) i) (eFM δ (T (yOf δ χ)) i) ≠ 0
    rw [e, InhabJ8Good.compress_split]
    exact quadPole_ne_mk δ _ (xV δ T i) χ _ (hmem _ List.mem_cons_self)
  -- the four keys
  have hK : ∀ l ∈ (hKeys : List (List (CoeffExpr (ZMod p)))),
      dK δ (chalsALJ8 δ χ) (T (yOf δ χ)) (HQ.denKeyQ δ l) i ≠ 0 := by
    intro l hl
    show (HQ.denKeyQ δ l).ev δ (eKM δ (chalsALJ8 δ χ) (T (yOf δ χ)) i) (eFM δ (T (yOf δ χ)) i) ≠ 0
    rw [AxisTeleJ9.denKeyQ_evL δ _ _ 8 l (hKeys_len l hl), coinsQ_AL, InhabJ8Good.compress_split]
    exact quadPole_ne δ InhabJ8Good.c12 (xH δ T l i) χ _ (ρH_re δ χ)
      (hmem _ (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨l, hl, rfl⟩)))
  exact ⟨hV, hK _ (by simp [hKeys]), hK _ (by simp [hKeys]), hK _ (by simp [hKeys]), hK _ (by simp [hKeys])⟩

/-- **`hden` of the stage 1–3 theorem** at `chalsALJ8` and the table `T y`, from `famAL` at `N = n`
(unconditional: every row, active or not). -/
theorem hden_of_famAL {n : ℕ} (χ : Coins frameJ8 K) (hχ : ∀ e ∈ famAL δ T n, χ ∉ e.ev) :
    ∀ i : Fin n,
      ((rowAt δ (T (yOf δ χ)) i).1.aV ≠ 0 → dV δ (chalsALJ8 δ χ) (T (yOf δ χ)) i ≠ 0) ∧
      ((rowAt δ (T (yOf δ χ)) i).1.sH + (rowAt δ (T (yOf δ χ)) i).1.sP ≠ 0 →
        dR δ (chalsALJ8 δ χ) (T (yOf δ χ)) i ≠ 0 ∧ dO δ (chalsALJ8 δ χ) (T (yOf δ χ)) i ≠ 0) ∧
      ((rowAt δ (T (yOf δ χ)) i).1.sH ≠ 0 →
        dJ δ (chalsALJ8 δ χ) (T (yOf δ χ)) i ≠ 0 ∧ dX δ (chalsALJ8 δ χ) (T (yOf δ χ)) i ≠ 0) := by
  intro i
  obtain ⟨h1, h2, h3, h4, h5⟩ := famAL_good δ T n χ hχ i i.isLt
  exact ⟨fun _ => h1, fun _ => ⟨h2, h3⟩, fun _ => ⟨h4, h5⟩⟩

/-! ## The carry: `B.Good`, the weights, `epsC` and the figure -/

/-- A coin outside every event of `badOf (L ++ famAL)` is outside every ALU pole event. -/
theorem good_famAL (L : List (BadSpec K)) (N : ℕ) (χ : Coins frameJ8 K)
    (h : ∀ e ∈ badOf (L ++ famAL δ T N), χ ∉ e.1) : ∀ e ∈ famAL δ T N, χ ∉ e.ev :=
  fun e he => h _ (List.mem_map.mpr ⟨e, List.mem_append_right _ he, rfl⟩)

/-- The weights of an extended bad list stay valid (`wt`). -/
theorem wt_famAL (L : List (BadSpec K)) (hL : ∀ s ∈ L, s.OK) (N : ℕ) :
    ∀ e ∈ badOf (L ++ famAL δ T N), (e.1.card : ℚ) / Fintype.card (Coins frameJ8 K) ≤ e.2 :=
  wt_badOf _ fun s hs => (List.mem_append.mp hs).elim (hL s) (famAL_OK δ T N s)

theorem costL_append (L M : List (BadSpec K)) : costL (L ++ M) = costL L + costL M := by
  simp [costL, List.map_append, List.sum_append]

/-- **`epsC` of the extended list**: `(costL L + 5 N) / |𝕂|`. -/
theorem eps_famAL (L : List (BadSpec K)) (N : ℕ) :
    ((badOf (L ++ famAL δ T N)).map Prod.snd).sum = ((costL L + 5 * N : ℕ) : ℚ) / Fintype.card K := by
  rw [sum_w_badOf, costL_append, famAL_cost]

/-- **The figure carries**: if the base list costs `≤ 2^67` and `N ≤ 2^31`, the extended list's error is
`< 2^-120` at `|𝕂| = cK` (the J-9 A list costs `≤ 2^66 + 2^63`, `figA`). -/
theorem fig_famAL (L : List (BadSpec K)) (N : ℕ) (hL : costL L ≤ 2 ^ 67) (hN : N ≤ 2 ^ 31)
    (hK : Fintype.card K = VclL.Events.cK) :
    ((badOf (L ++ famAL δ T N)).map Prod.snd).sum < 1 / 2 ^ 120 := by
  rw [eps_famAL]
  refine cost_div_lt _ ?_ hK
  have e67 : (2 : ℕ) ^ 67 = 147573952589676412928 := by norm_num
  have e68 : (2 : ℕ) ^ 68 = 295147905179352825856 := by norm_num
  have e31 : (2 : ℕ) ^ 31 = 2147483648 := by norm_num
  omega

end Poles

end

end Nock.NockVMROM.Thm54.VclL.Handle.AluPoles
