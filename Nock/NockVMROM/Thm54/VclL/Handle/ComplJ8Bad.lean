/-
  Nock/NockVMROM/Thm54/VclL/Handle/ComplJ8Bad.lean

  **The honest bad events, their weights, the
  `goodC` extraction and the Goldilocks figure.**  Generic over the bad-event list: each chip lane exports its denominators as "covered by an event of
  the list" (`DenCovered`), and the list is built from two kinds of event only.

  * **`BadSpec.pin i g`**: coordinate `χ_i` equals `g χ`, where `g` does not read coordinate `i` (`ReadsOff i g`).
    Weight `1/|K|` (`InhabJ8Good.card_pin`).  The pole shape `ρ′ + x` with `Re ρ′ = χ_i` and `x` pole-free is
    `quadPole i x` (`quadPole_ne`: outside the event the denominator is non-zero).
  * **`BadSpec.ord i N`**: the coin `χ_i` has multiplicative order `< N` (a walk-coin order).  Weight `N²/|K|`
    (`HonestEpsVS.orderBad_card`).
  * `badOf L` = the `(event, weight)` list; **`wt_badOf`** is the obligation `wt` for `B.bad = badOf L`.
  * **`epsC_badOf`**: `ε_c = cost L / |K|` with `cost` = `#pins + Σ N²`.
  * **`goodC_of_cover`**: the obligation `goodC` from (i) `ord 13 |W| ∈ L` (the compute walk coin `αJ = χ₁₃`,
    `αJ_eq`) and (ii) every compute slot denominator covered by an event of `L` (or the slot inactive).
  * **`fig_of_cost`** / **`fig_of_counts`**: the obligation `fig` from `cost L ≤ 2^68` (e.g. `≤ 2^66` pins and
    `≤ 4` walk orders of `N ≤ 2^31`): `ε_c ≤ 2^68/|K| ≤ 2^68/2^189 < 2^-120`.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8
import Nock.NockVMROM.Thm54.VclL.Handle.InhabJ8Good
import Nock.NockVMROM.Thm54.VclL.Handle.HonestEpsVSQ

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Bad

open Nock Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.SVFrame Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8
open Nock.NockVMROM.Thm54.CoordinateBasis
open Nock.NockVMROM.Thm54.VclL.Compute.LogUp (limbVal)
open Module Nock.NockVMROM.Thm54.VclL.Handle.VerJ8
open Nock.NockVMROM.Thm54.VclL.Handle.BalanceQ (liftRec)

noncomputable section

/-! ## 1. The two event kinds and their weights -/

section Spec
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

/-- `g` does not read coordinate `i`. -/
def ReadsOff {β : Type} (i : Fin frameJ8.n) (g : Coins frameJ8 K → β) : Prop :=
  ∀ χ χ' : Coins frameJ8 K, (∀ k, k ≠ i → χ k = χ' k) → g χ = g χ'

inductive BadSpec (K : Type)
  | pin (i : Fin frameJ8.n) (g : Coins frameJ8 K → K)
  | ord (i : Fin frameJ8.n) (N : ℕ)

namespace BadSpec

/-- The event. -/
def ev : BadSpec K → Finset (Coins frameJ8 K)
  | pin i g => Finset.univ.filter fun χ => χ i = g χ
  | ord i N => Finset.univ.filter fun χ => orderOf (χ i) < N

/-- The numerator of the weight (the weight is `cost / |K|`). -/
def cost : BadSpec K → ℕ
  | pin _ _ => 1
  | ord _ N => N * N

/-- The weight. -/
def w (s : BadSpec K) : ℚ := (s.cost : ℚ) / Fintype.card K

def OK : BadSpec K → Prop
  | pin i g => ReadsOff i g
  | ord _ _ => True

end BadSpec

/-- The `(event, weight)` list of a specification list (the shape of `HonestJ8.bad`). -/
def badOf (L : List (BadSpec K)) : List (Finset (Coins frameJ8 K) × ℚ) := L.map fun s => (s.ev, s.w)

/-- The total cost. -/
def costL (L : List (BadSpec K)) : ℕ := (L.map BadSpec.cost).sum

/-- `{χ | χ_i ∈ S}` has `≤ |S| · |K|^18` elements. -/
theorem card_coord_mem (i : Fin frameJ8.n) (S : Finset K) :
    (Finset.univ.filter fun χ : Coins frameJ8 K => χ i ∈ S).card ≤ S.card * Fintype.card K ^ 18 := by
  have hsub : (Finset.univ.filter fun χ : Coins frameJ8 K => χ i ∈ S) ⊆
      S.biUnion fun a => Finset.univ.filter fun χ : Coins frameJ8 K => χ i = (fun _ => a) χ := by
    intro χ hχ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hχ
    exact Finset.mem_biUnion.mpr ⟨χ i, hχ, by simp⟩
  refine (Finset.card_le_card hsub).trans ((Finset.card_biUnion_le).trans ?_)
  calc ∑ a ∈ S, (Finset.univ.filter fun χ : Coins frameJ8 K => χ i = (fun _ => a) χ).card
      ≤ ∑ _a ∈ S, Fintype.card K ^ 18 :=
        Finset.sum_le_sum fun a _ => InhabJ8Good.card_pin i (fun _ => a) fun _ _ _ => rfl
    _ = S.card * Fintype.card K ^ 18 := by rw [Finset.sum_const, smul_eq_mul]

theorem BadSpec.card_ev (s : BadSpec K) (hs : s.OK) : s.ev.card ≤ s.cost * Fintype.card K ^ 18 := by
  cases s with
  | pin i g => simpa [BadSpec.ev, BadSpec.cost] using InhabJ8Good.card_pin i g hs
  | ord i N =>
    have h := card_coord_mem (K := K) i (Finset.univ.filter fun a : K => orderOf a < N)
    have h2 := FrameVS.orderBad_card (K := K) N
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h
    exact h.trans (Nat.mul_le_mul_right _ h2)

/-- **Each event's probability is at most its weight.** -/
theorem BadSpec.prob_le (s : BadSpec K) (hs : s.OK) :
    (s.ev.card : ℚ) / Fintype.card (Coins frameJ8 K) ≤ s.w := by
  have hK : (0 : ℚ) < Fintype.card K := by exact_mod_cast Fintype.card_pos
  rw [InhabJ8Good.card_coins, BadSpec.w, div_le_div_iff₀ (by positivity) hK]
  have h := s.card_ev hs
  have h' : (s.ev.card : ℚ) ≤ (s.cost : ℚ) * (Fintype.card K : ℚ) ^ 18 := by exact_mod_cast h
  calc (s.ev.card : ℚ) * Fintype.card K ≤ (s.cost : ℚ) * (Fintype.card K : ℚ) ^ 18 * Fintype.card K :=
        mul_le_mul_of_nonneg_right h' hK.le
    _ = (s.cost : ℚ) * ((Fintype.card K ^ 19 : ℕ) : ℚ) := by push_cast; ring

/-- **The obligation `wt`** for a list built by `badOf`. -/
theorem wt_badOf (L : List (BadSpec K)) (hL : ∀ s ∈ L, s.OK) :
    ∀ e ∈ badOf L, (e.1.card : ℚ) / Fintype.card (Coins frameJ8 K) ≤ e.2 := by
  intro e he
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp he
  exact s.prob_le (hL s hs)

/-- **The completeness error of `badOf L`** is `cost L / |K|`. -/
theorem sum_w_badOf (L : List (BadSpec K)) :
    ((badOf L).map Prod.snd).sum = (costL L : ℚ) / Fintype.card K := by
  induction L with
  | nil => simp [badOf, costL]
  | cons s L ih =>
    simp only [badOf, List.map_cons, List.sum_cons, List.map_map] at ih ⊢
    rw [show (Prod.snd ∘ fun s : BadSpec K => (s.ev, s.w)) = BadSpec.w from rfl] at ih ⊢
    rw [ih]
    simp only [costL, List.map_cons, List.sum_cons, BadSpec.w, Nat.cast_add, add_div]

theorem good_pin {L : List (BadSpec K)} {χ : Coins frameJ8 K} (hχ : ∀ e ∈ badOf L, χ ∉ e.1)
    {i : Fin frameJ8.n} {g : Coins frameJ8 K → K} (hs : BadSpec.pin i g ∈ L) : χ i ≠ g χ := by
  intro h
  exact hχ _ (List.mem_map.mpr ⟨_, hs, rfl⟩) (by simp [BadSpec.ev, h])

/-- Outside every event of `badOf L`: a walk coin has order `≥ N`. -/
theorem good_ord {L : List (BadSpec K)} {χ : Coins frameJ8 K} (hχ : ∀ e ∈ badOf L, χ ∉ e.1)
    {i : Fin frameJ8.n} {N : ℕ} (hs : BadSpec.ord i N ∈ L) : N ≤ orderOf (χ i) := by
  by_contra h
  exact hχ _ (List.mem_map.mpr ⟨_, hs, rfl⟩) (by simp [BadSpec.ev]; omega)

/-- Outside every event of `badOf L`: no event of `L` contains `χ`. -/
theorem good_spec {L : List (BadSpec K)} {χ : Coins frameJ8 K} (hχ : ∀ e ∈ badOf L, χ ∉ e.1)
    {s : BadSpec K} (hs : s ∈ L) : χ ∉ s.ev :=
  hχ _ (List.mem_map.mpr ⟨_, hs, rfl⟩)

end Spec

/-! ## 2. The 𝕂′ pole shape -/

section Pole
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [Fintype K] [DecidableEq K]
  (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

/-- **The pole event of a pole-free part `x`** at the pole whose real part is `χ_i`: `χ_i = −Re x`. -/
def quadPole (i : Fin frameJ8.n) (x : Coins frameJ8 K → 𝕂′) : BadSpec K :=
  BadSpec.pin i fun χ => -(Quad.re _ (x χ))

theorem quadPole_OK (i : Fin frameJ8.n) (x : Coins frameJ8 K → 𝕂′) (hx : ReadsOff i x) :
    (quadPole δ i x).OK := fun χ χ' h => by simp only [hx χ χ' h]

/-- **Outside the pole event the denominator is non-zero**: `Re ρ′ = χ_i`, `χ ∉ quadPole i x` ⇒ `ρ′ + x χ ≠ 0`. -/
theorem quadPole_ne (i : Fin frameJ8.n) (x : Coins frameJ8 K → 𝕂′) (χ : Coins frameJ8 K) (ρ : 𝕂′)
    (hre : Quad.re _ ρ = χ i) (hχ : χ ∉ (quadPole δ i x).ev) : ρ + x χ ≠ 0 := by
  intro h
  apply hχ
  simp only [quadPole, BadSpec.ev, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [← hre]
  rw [← Quad.mk_re_im _ ρ] at h
  exact InhabJ8Good.pole_pin δ _ _ _ h

/-- The same at a pole `Quad.mk (χ_i) c`. -/
theorem quadPole_ne_mk (i : Fin frameJ8.n) (x : Coins frameJ8 K → 𝕂′) (χ : Coins frameJ8 K) (c : K)
    (hχ : χ ∉ (quadPole δ i x).ev) : Quad.mk _ (χ i) c + x χ ≠ 0 :=
  quadPole_ne δ i x χ _ (Quad.re_mk _ _ _) hχ

end Pole


/-! ## 2b. LogUp pole families (one event per record) and the J chip's instance -/

section IOPoles
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [Fintype K] [DecidableEq K]
  (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

/-- **The pole events of a LogUp record list** at coins `(γ χ, ρ χ)` with `Re ρ = χ_i`: one `quadPole` per
record, on the pole-free part `compress (γ, 0) v`.  Any chip's denominator list (a function of the honest data,
not of `χ`) becomes bad events by this one definition. -/
def ioPoles {m : ℕ} (i : Fin frameJ8.n) (γ : Coins frameJ8 K → 𝕂′) (R : List (Fin m → 𝕂′)) :
    List (BadSpec K) :=
  R.map fun v => quadPole δ i fun χ => FiniteIO.compress (⟨γ χ, 0⟩ : FiniteIO.IOCoins 𝕂′) v

theorem ioPoles_OK {m : ℕ} (i : Fin frameJ8.n) (γ : Coins frameJ8 K → 𝕂′) (R : List (Fin m → 𝕂′))
    (hγ : ReadsOff i γ) : ∀ s ∈ ioPoles δ i γ R, s.OK := by
  intro s hs
  obtain ⟨v, -, rfl⟩ := List.mem_map.mp hs
  exact quadPole_OK δ i _ fun χ χ' h => by simp only [hγ χ χ' h]

/-- **Outside the pole events every denominator of the list is non-zero.** -/
theorem ioPoles_good {m : ℕ} (i : Fin frameJ8.n) (γ ρ : Coins frameJ8 K → 𝕂′) (R : List (Fin m → 𝕂′))
    (hre : ∀ χ, Quad.re _ (ρ χ) = χ i) (χ : Coins frameJ8 K) (hχ : ∀ s ∈ ioPoles δ i γ R, χ ∉ s.ev) :
    ∀ v ∈ R, FiniteIO.compress (⟨γ χ, ρ χ⟩ : FiniteIO.IOCoins 𝕂′) v ≠ 0 := by
  intro v hv
  rw [InhabJ8Good.compress_split δ]
  exact quadPole_ne δ i _ χ (ρ χ) (hre χ) (hχ _ (List.mem_map.mpr ⟨v, hv, rfl⟩))

/-- The handle coins `γH = (χ₁₁, χ₁₅)`, `ρH = (χ₁₂, χ₁₆)` at `frameJ8`. -/
def γH (χ : Coins frameJ8 K) : 𝕂′ := Quad.mk _ (χ ⟨11, by decide⟩) (χ ⟨15, by decide⟩)
def ρH (χ : Coins frameJ8 K) : 𝕂′ := Quad.mk _ (χ ⟨12, by decide⟩) (χ ⟨16, by decide⟩)

theorem γH_readsOff : ReadsOff (K := K) InhabJ8Good.c12 (γH δ) := fun χ χ' h => by
  simp only [γH]; rw [h _ (by decide), h _ (by decide)]

theorem ρH_re (χ : Coins frameJ8 K) : Quad.re _ (ρH δ χ) = χ InhabJ8Good.c12 := Quad.re_mk _ _ _

/-- **The J chip's tagged and export coins are the handle coins** (`chalsJJ8`, `coinsJ`, `coinsJX`). -/
theorem coinsJ_J8 (χ : Coins frameJ8 K) :
    Nock.Jet.RapJetJ8.coinsJ δ (chalsJJ8 χ) = (⟨γH δ χ, ρH δ χ⟩ : FiniteIO.IOCoins 𝕂′) ∧
      Nock.Jet.RapJetJ8.coinsJX δ (chalsJJ8 χ) = (⟨γH δ χ, ρH δ χ⟩ : FiniteIO.IOCoins 𝕂′) := by
  refine ⟨?_, ?_⟩ <;>
  simp [Nock.Jet.RapJetJ8.coinsJ, Nock.Jet.RapJetJ8.coinsJX, chalsJJ8, γH, ρH, toVSQ, FrameVSQ.cGamHi,
    FrameVSQ.cRhoHi]

/-- **The J chip's pole condition (L4's `JPole` hypotheses, in `noPole`'s conclusion shape) outside the J pole
events**: `KT` / `KX` are the J tagged / export key lists (L4's `jKeysT rows` / `jKeysX rows`). -/
theorem jNoPole (KT KX : List (List (ZMod p))) (χ : Coins frameJ8 K)
    (hχ : ∀ s ∈ ioPoles δ InhabJ8Good.c12 (γH δ) (KT.map fun κ => liftRec (L := 𝕂′) (Nock.Jet.RapJetJ8.keyK (K := K) 8 κ)) ++
      ioPoles δ InhabJ8Good.c12 (γH δ) (KX.map fun κ => liftRec (L := 𝕂′) (Nock.Jet.RapJetJ8.keyK (K := K) 5 κ)),
      χ ∉ s.ev) :
    (∀ κ ∈ KT, FiniteIO.compress (Nock.Jet.RapJetJ8.coinsJ δ (chalsJJ8 χ))
        (liftRec (L := 𝕂′) (Nock.Jet.RapJetJ8.keyK (K := K) 8 κ)) ≠ 0) ∧
    (∀ κ ∈ KX, FiniteIO.compress (Nock.Jet.RapJetJ8.coinsJX δ (chalsJJ8 χ))
        (liftRec (L := 𝕂′) (Nock.Jet.RapJetJ8.keyK (K := K) 5 κ)) ≠ 0) := by
  obtain ⟨h1, h2⟩ := coinsJ_J8 δ χ
  rw [h1, h2]
  refine ⟨fun κ hκ => ?_, fun κ hκ => ?_⟩
  · exact ioPoles_good δ _ (γH δ) (ρH δ) _ (ρH_re δ) χ (fun s hs => hχ s (List.mem_append_left _ hs)) _
      (List.mem_map.mpr ⟨κ, hκ, rfl⟩)
  · exact ioPoles_good δ _ (γH δ) (ρH δ) _ (ρH_re δ) χ (fun s hs => hχ s (List.mem_append_right _ hs)) _
      (List.mem_map.mpr ⟨κ, hκ, rfl⟩)

end IOPoles

/-! ## 3. `goodC` -/

section GoodC
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {Rg : Nock.Jet.VerifiedRegistry} {fuel : ℕ} {s f r : Noun}

/-- The compute walk coin `αJ` is the coin `χ₁₃`. -/
theorem αJ_eq (χ : Coins frameJ8 K) : αJ b χ = χ ⟨13, by decide⟩ := by
  refine InhabJ8Comp.limbVal_coord b _ _ _ fun k => ?_
  fin_cases k <;> simp [VerJ8.chalVJ8, FrameVSQ.chalVHQ, FrameVSQ.coinHQ, FrameVS.coinH, FrameVSQ.toVS, toVSQ,
    ChipH.chalAlphaW, FrameVS.cAlphaW]

/-- The compute slot denominators at `χ` are covered by `L`: every slot of every row is inactive (`A = 0`) or its
denominator is non-zero outside some event of `L` (each chip lane exports this; `quadPole_ne_mk` is the usual
proof). -/
def DenCovered (B : HonestJ8 p K δ Rg fuel s f r) (L : List (BadSpec K)) : Prop :=
  ∀ χ : Coins frameJ8 K, ∀ j < B.Pb.n, ∀ S ∈ Nock.NockVMROM.Thm54.VclL.Handle.ChipHX.slotsX (F := ZMod p),
    HonestSlotX.aVal b δ S (VclL.HonestTraceX.env0 B.H B.pd B.W (chalVJ8 b χ) (pubJ δ b B χ) j) = 0 ∨
    ∃ e ∈ L, χ ∉ e.ev →
      HonestSlotX.dVal b δ S (VclL.HonestTraceX.env0 B.H B.pd B.W (chalVJ8 b χ) (pubJ δ b B χ) j) ≠ 0

/-- **The obligation `goodC`** from the bad list `badOf L`: the walk-coin order event of the BFS length on
`χ₁₃`, and the compute slot denominators covered by `L`. -/
theorem goodC_of_cover (B : HonestJ8 p K δ Rg fuel s f r) (L : List (BadSpec K)) (hbad : B.bad = badOf L)
    (hord : BadSpec.ord ⟨13, by decide⟩ B.W.length ∈ L) (hcov : DenCovered δ b B L) :
    ∀ χ, B.Good χ → B.W.length ≤ orderOf (αJ b χ) ∧
      ∀ j < B.Pb.n, ∀ S ∈ Nock.NockVMROM.Thm54.VclL.Handle.ChipHX.slotsX (F := ZMod p),
        HonestSlotX.dVal b δ S (VclL.HonestTraceX.env0 B.H B.pd B.W (chalVJ8 b χ) (pubJ δ b B χ) j) ≠ 0 ∨
          HonestSlotX.aVal b δ S (VclL.HonestTraceX.env0 B.H B.pd B.W (chalVJ8 b χ) (pubJ δ b B χ) j) = 0 := by
  intro χ hχ
  have hg : ∀ e ∈ badOf L, χ ∉ e.1 := by rw [← hbad]; exact hχ
  refine ⟨?_, fun j hj S hS => ?_⟩
  · rw [αJ_eq]; exact good_ord hg hord
  · rcases hcov χ j hj S hS with h0 | ⟨e, he, hne⟩
    · exact Or.inr h0
    · exact Or.inl (hne (good_spec hg he))

end GoodC

/-! ## 4. The figure -/

section Fig
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] (δ : ZMod p) [Fintype K]
  [DecidableEq K] {Rg : Nock.Jet.VerifiedRegistry} {fuel : ℕ} {s f r : Noun}

/-- **`ε_c` of `badOf L`** is `cost L / |K|`. -/
theorem epsC_badOf (B : HonestJ8 p K δ Rg fuel s f r) (L : List (BadSpec K)) (hbad : B.bad = badOf L) :
    B.epsC = (costL L : ℚ) / Fintype.card K := by
  rw [HonestJ8.epsC, hbad, sum_w_badOf]

/-- `cost ≤ 2^68` and `|K| = cK` give `ε_c < 2^-120`. -/
theorem cost_div_lt (c : ℕ) (hc : c ≤ 2 ^ 68) (hK : Fintype.card K = VclL.Events.cK) :
    (c : ℚ) / Fintype.card K < 1 / 2 ^ 120 := by
  have hK189 : (2 : ℚ) ^ 189 ≤ Fintype.card K := by
    rw [hK]; exact_mod_cast FrameVSQ.two_pow_189_le_cK
  have hKpos : (0 : ℚ) < Fintype.card K := lt_of_lt_of_le (by positivity) hK189
  have hc' : (c : ℚ) ≤ 2 ^ 68 := by exact_mod_cast hc
  rw [div_lt_div_iff₀ hKpos (by positivity)]
  calc (c : ℚ) * 2 ^ 120 ≤ 2 ^ 68 * 2 ^ 120 := by gcongr
    _ < 1 * 2 ^ 189 := by norm_num
    _ ≤ 1 * Fintype.card K := by gcongr

/-- **The obligation `fig`** from a cost bound at `≤ 2^31` rows. -/
theorem fig_of_cost (B : HonestJ8 p K δ Rg fuel s f r) (L : List (BadSpec K)) (hbad : B.bad = badOf L)
    (hcost : RowsLe31 B.Pb → costL L ≤ 2 ^ 68) :
    p = Nock.Atoms.p → Fintype.card K = VclL.Events.cK → RowsLe31 B.Pb → B.epsC < 1 / 2 ^ 120 := by
  intro _ hK hrows
  rw [epsC_badOf δ B L hbad]
  exact cost_div_lt _ (hcost hrows) hK

def nPins : List (BadSpec K) → ℕ
  | [] => 0
  | BadSpec.pin _ _ :: L => nPins L + 1
  | BadSpec.ord _ _ :: L => nPins L

def nOrds : List (BadSpec K) → ℕ
  | [] => 0
  | BadSpec.pin _ _ :: L => nOrds L
  | BadSpec.ord _ _ :: L => nOrds L + 1

/-- `cost ≤ #pins + #orders · M²` when every order bound is `≤ M`. -/
theorem costL_le (L : List (BadSpec K)) (M : ℕ) (hM : ∀ i N, BadSpec.ord i N ∈ L → N ≤ M) :
    costL L ≤ nPins L + nOrds L * (M * M) := by
  induction L with
  | nil => simp [costL, nPins, nOrds]
  | cons s L ih =>
    have ih' := ih fun i N h => hM i N (List.mem_cons_of_mem _ h)
    cases s with
    | pin i g => simp only [costL, List.map_cons, List.sum_cons, nPins, nOrds, BadSpec.cost] at ih' ⊢; omega
    | ord i N =>
      have hN := hM i N List.mem_cons_self
      simp only [costL, List.map_cons, List.sum_cons, nPins, nOrds, BadSpec.cost] at ih' ⊢
      have : N * N ≤ M * M := Nat.mul_le_mul hN hN
      nlinarith

theorem fig_of_counts (B : HonestJ8 p K δ Rg fuel s f r) (L : List (BadSpec K)) (hbad : B.bad = badOf L)
    (hP : RowsLe31 B.Pb → nPins L ≤ 2 ^ 66) (hO : nOrds L ≤ 4)
    (hN : RowsLe31 B.Pb → ∀ i N, BadSpec.ord i N ∈ L → N ≤ 2 ^ 31) :
    p = Nock.Atoms.p → Fintype.card K = VclL.Events.cK → RowsLe31 B.Pb → B.epsC < 1 / 2 ^ 120 :=
  fig_of_cost δ B L hbad fun hr => by
    have h := costL_le L (2 ^ 31) (hN hr)
    have h1 := hP hr
    have h2 : nOrds L * (2 ^ 31 * 2 ^ 31) ≤ 4 * (2 ^ 31 * 2 ^ 31) := Nat.mul_le_mul_right _ hO
    omega

end Fig

/-! ## 5. Assembling the list: counts per family -/

section Assemble
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

/-- A coin-vanishing event `χ_i = 0` (weight `1/|K|`). -/
def zeroEv (i : Fin frameJ8.n) : BadSpec K := BadSpec.pin i fun _ => 0

theorem zeroEv_OK (i : Fin frameJ8.n) : (zeroEv (K := K) i).OK := fun _ _ _ => rfl

theorem nPins_append (L M : List (BadSpec K)) : nPins (L ++ M) = nPins L + nPins M := by
  induction L with
  | nil => simp [nPins]
  | cons s L ih => cases s <;> simp only [List.cons_append, nPins, ih] <;> omega

theorem nOrds_append (L M : List (BadSpec K)) : nOrds (L ++ M) = nOrds L + nOrds M := by
  induction L with
  | nil => simp [nOrds]
  | cons s L ih => cases s <;> simp only [List.cons_append, nOrds, ih] <;> omega

theorem nPins_map_pin {β : Type} (R : List β) (i : β → Fin frameJ8.n) (g : β → Coins frameJ8 K → K) :
    nPins (R.map fun v => BadSpec.pin (i v) (g v)) = R.length ∧
      nOrds (R.map fun v => BadSpec.pin (i v) (g v)) = 0 := by
  induction R with
  | nil => simp [nPins, nOrds]
  | cons v R ih => simp only [List.map_cons, nPins, nOrds, List.length_cons, ih]; simp

theorem nPins_flatten (Ls : List (List (BadSpec K))) : nPins Ls.flatten = (Ls.map nPins).sum := by
  induction Ls with
  | nil => simp [nPins]
  | cons L Ls ih => simp [nPins_append, ih]

theorem nOrds_flatten (Ls : List (List (BadSpec K))) : nOrds Ls.flatten = (Ls.map nOrds).sum := by
  induction Ls with
  | nil => simp [nOrds]
  | cons L Ls ih => simp [nOrds_append, ih]

/-- A list without order events has `nOrds = 0`. -/
theorem nOrds_eq_zero (L : List (BadSpec K)) (h : ∀ s ∈ L, ∀ i N, s ≠ BadSpec.ord i N) : nOrds L = 0 := by
  induction L with
  | nil => rfl
  | cons s L ih =>
    cases s with
    | pin i g => exact ih fun t ht => h t (List.mem_cons_of_mem _ ht)
    | ord i N => exact absurd rfl (h _ List.mem_cons_self i N)

def badList (ords : List (Fin frameJ8.n × ℕ)) (fams : List (List (BadSpec K))) : List (BadSpec K) :=
  ords.map (fun o => BadSpec.ord o.1 o.2) ++ fams.flatten

theorem badList_OK (ords : List (Fin frameJ8.n × ℕ)) (fams : List (List (BadSpec K)))
    (h : ∀ L ∈ fams, ∀ s ∈ L, s.OK) : ∀ s ∈ badList ords fams, s.OK := by
  intro s hs
  rcases List.mem_append.mp hs with h1 | h2
  · obtain ⟨o, -, rfl⟩ := List.mem_map.mp h1; trivial
  · obtain ⟨L, hL, hsL⟩ := List.mem_flatten.mp h2; exact h L hL s hsL

theorem nOrds_ords (ords : List (Fin frameJ8.n × ℕ)) :
    nPins (ords.map fun o => BadSpec.ord (K := K) o.1 o.2) = 0 ∧
      nOrds (ords.map fun o => BadSpec.ord (K := K) o.1 o.2) = ords.length := by
  induction ords with
  | nil => simp [nPins, nOrds]
  | cons o ords ih => simp only [List.map_cons, nPins, nOrds, List.length_cons, ih]; simp

/-- **The counts of `badList`**: `#pins = Σ_fam #pins`, `#orders = |ords|` when every family is pins only. -/
theorem badList_counts (ords : List (Fin frameJ8.n × ℕ)) (fams : List (List (BadSpec K)))
    (h0 : ∀ L ∈ fams, nOrds L = 0) :
    nPins (badList ords fams) = (fams.map nPins).sum ∧ nOrds (badList ords fams) = ords.length := by
  have hz : (fams.map nOrds).sum = 0 := by
    induction fams with
    | nil => rfl
    | cons L Ls ih =>
      simp only [List.map_cons, List.sum_cons, h0 L List.mem_cons_self,
        ih fun M hM => h0 M (List.mem_cons_of_mem _ hM)]
  refine ⟨?_, ?_⟩
  · rw [badList, nPins_append, (nOrds_ords ords).1, nPins_flatten, zero_add]
  · rw [badList, nOrds_append, (nOrds_ords ords).2, nOrds_flatten, hz, add_zero]

/-- The order bounds of `badList` are those of `ords` (families have no order event). -/
theorem badList_ord_mem (ords : List (Fin frameJ8.n × ℕ)) (fams : List (List (BadSpec K)))
    (h0 : ∀ L ∈ fams, ∀ s ∈ L, ∀ i N, s ≠ BadSpec.ord i N) (i : Fin frameJ8.n) (N : ℕ)
    (hm : BadSpec.ord i N ∈ badList ords fams) : (i, N) ∈ ords := by
  rcases List.mem_append.mp hm with h1 | h2
  · obtain ⟨o, ho, he⟩ := List.mem_map.mp h1
    cases he; exact ho
  · obtain ⟨L, hL, hsL⟩ := List.mem_flatten.mp h2
    exact absurd rfl (h0 L hL _ hsL i N)

end Assemble

section FigList
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] (δ : ZMod p) [Fintype K]
  [DecidableEq K] {Rg : Nock.Jet.VerifiedRegistry} {fuel : ℕ} {s f r : Noun}

/-- **The obligation `fig` for an assembled `badList`**: families are pins only, their pin counts sum to
`≤ 2^66` at `≤ 2^31` rows, at most `4` walk orders each of bound `≤ 2^31`. -/
theorem fig_badList (B : HonestJ8 p K δ Rg fuel s f r) (ords : List (Fin frameJ8.n × ℕ))
    (fams : List (List (BadSpec K))) (hbad : B.bad = badOf (badList ords fams))
    (hfam : ∀ L ∈ fams, ∀ s ∈ L, ∀ i N, s ≠ BadSpec.ord i N)
    (hP : RowsLe31 B.Pb → (fams.map nPins).sum ≤ 2 ^ 66) (hO : ords.length ≤ 4)
    (hN : RowsLe31 B.Pb → ∀ o ∈ ords, o.2 ≤ 2 ^ 31) :
    p = Nock.Atoms.p → Fintype.card K = VclL.Events.cK → RowsLe31 B.Pb → B.epsC < 1 / 2 ^ 120 := by
  have h0 : ∀ L ∈ fams, nOrds L = 0 := fun L hL => nOrds_eq_zero L (hfam L hL)
  obtain ⟨hcP, hcO⟩ := badList_counts ords fams h0
  exact fig_of_counts δ B _ hbad (fun hr => hcP ▸ hP hr) (hcO ▸ hO)
    (fun hr i N hm => hN hr (i, N) (badList_ord_mem ords fams hfam i N hm))

end FigList

end

end Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Bad
