/-
  Nock/NockVMROM/Thm54/VclL/Handle/ComplJ8CompPole.lean

-/
import Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Comp
import Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Bad

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxRecDepth 100000

namespace Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8CompPole

open Nock Nock.Noun Nock.Walk Nock.Edit Nock.Edit.GenX Nock.Reified Nock.Framework Module Polynomial
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler
open Nock.NockVMROM.Thm54.T0Tower Nock.NockVMROM.Thm54.T0TowerFP Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.VclL.Compute.LogUp Nock.NockVMROM.Thm54.VclL.Compute.TowerD
open Nock.NockVMROM.Thm54.VclL.Handle.ChipH (cc notC selS consCol)
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHX Nock.NockVMROM.Thm54.VclL.Handle.HonestWalkX
open Nock.NockVMROM.Thm54.VclL.Handle.HonestSlotX
open Nock.NockVMROM.Thm54.VclL.HonestTraceX
open Nock.NockVMROM.Thm54.VclL.Handle.FrameVS
open Nock.NockVMROM.Thm54.VclL.Handle.FrameVSQ
open Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8 (frameJ8 toVSQ)
open Nock.NockVMROM.Thm54.VclL.Handle.VerJ8
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Bad
open Nock.NockVMROM.Thm54.VclL.Handle.DenXJ8
open Nock.NockVMROM.Thm54.FiniteIO Nock.NockVMROM.Thm54.SVFrame
open Nock.NockVMROM.Thm54.VclL.Handle.BalanceQ (liftRec)

noncomputable section

section Gen
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

theorem dVal_expand (S : SlotX (ZMod p)) (e : Env (ZMod p)) :
    dVal b δ S e = (S.ents.map fun x => algebraMap (ZMod p) 𝕂′ (x.act.eval e) *
        Nock.NockVMROM.Thm54.VclL.Handle.TeleCQX.DX δ (gatherEnv b e) e x.rcd).sum +
      (match S.pair with
       | some (fl, a, b', _) => algebraMap (ZMod p) 𝕂′ (e.trace fl) *
           (Nock.NockVMROM.Thm54.VclL.Handle.TeleCQX.DX δ (gatherEnv b e) e a *
            Nock.NockVMROM.Thm54.VclL.Handle.TeleCQX.DX δ (gatherEnv b e) e b')
       | none => 0) := by
  simp only [dVal, slotDQ, qadd_val, Nock.NockVMROM.Thm54.VclL.Handle.ComputeSatHQ.sumQ_val, List.map_map,
    qmul_val, qlift_val, qconst_val]
  congr 1
  · congr 1
    refine List.map_congr_left fun x _ => ?_
    simp only [Function.comp, qmul_val, qlift_val]; rfl
  · rcases S.pair with _ | ⟨fl, a, b', _⟩
    · simp [qconst_val]
    · simp only [qmul_val, qlift_val]; rfl

theorem aVal_expand (S : SlotX (ZMod p)) (e : Env (ZMod p)) :
    aVal b δ S e = algebraMap (ZMod p) 𝕂′ ((S.ents.map fun x => x.act.eval e).sum) +
      (match S.pair with
       | some (fl, a, b', _) => algebraMap (ZMod p) 𝕂′ (e.trace fl) *
           (Nock.NockVMROM.Thm54.VclL.Handle.TeleCQX.DX δ (gatherEnv b e) e a +
            Nock.NockVMROM.Thm54.VclL.Handle.TeleCQX.DX δ (gatherEnv b e) e b')
       | none => 0) := by
  simp only [aVal, slotAQ, qadd_val, qlift_val, CoeffExpr.eval_sumList]
  congr 1
  rcases S.pair with _ | ⟨fl, a, b', _⟩
  · simp [qconst_val]
  · simp only [qmul_val, qlift_val, qadd_val]; rfl

theorem γH_eq (χ : Coins frameJ8 K) : γH δ χ = gamHQ δ (toVSQ χ) := by
  simp [γH, gamHQ, toVSQ, FrameVSQ.cGamHi]
theorem ρH_eq (χ : Coins frameJ8 K) : ρH δ χ = rhoHQ δ (toVSQ χ) := by
  simp [ρH, rhoHQ, toVSQ, FrameVSQ.cRhoHi]

/-- **A compute record's denominator is the handle pole plus a pole-free part.** -/
theorem den_split (e : Env (ZMod p)) (χ : Coins frameJ8 K) (hch : e.chal = chalVJ8 b χ) (r : List RE)
    (hr : r.length ≤ 8) :
    Nock.NockVMROM.Thm54.VclL.Handle.TeleCQX.DX δ (gatherEnv b e) e r =
      ρH δ χ + compress (⟨γH δ χ, 0⟩ : IOCoins 𝕂′) (liftRec (L := 𝕂′) (keyX (K := K) 8 r e)) := by
  rw [denQX_val δ _ _ r 8 hr]
  have hc : Nock.NockVMROM.Thm54.VclL.Handle.TeleCQ.coinsCQ δ (gatherEnv b e) =
      (⟨gamHQ δ (toVSQ χ), rhoHQ δ (toVSQ χ)⟩ : IOCoins 𝕂′) := by
    rw [← coinsCV_J8 δ b χ, ← hch]; rfl
  rw [hc, ← γH_eq, ← ρH_eq, InhabJ8Good.compress_split]

theorem sum_aff {α : Type} (l : List α) (a : α → ZMod p) (c : α → 𝕂′) (ρ : 𝕂′) :
    (l.map fun x => algebraMap (ZMod p) 𝕂′ (a x) * (ρ + c x)).sum =
      algebraMap (ZMod p) 𝕂′ ((l.map a).sum) * ρ + (l.map fun x => algebraMap (ZMod p) 𝕂′ (a x) * c x).sum := by
  induction l with
  | nil => simp
  | cons x l ih => simp only [List.map_cons, List.sum_cons, ih, map_add]; ring

theorem keyX_congr (e1 e2 : Env (ZMod p)) (h : e1.trace = e2.trace) (m : ℕ) (r : List RE) :
    keyX (K := K) m r e1 = keyX (K := K) m r e2 := by
  funext c; simp [keyX, keyXN, h]

/-- The pole-free part of a record at the row `eT` (a function of the coins through `γH` only). -/
def pf (eT : Env (ZMod p)) (r : List RE) (χ : Coins frameJ8 K) : 𝕂′ :=
  compress (⟨γH δ χ, 0⟩ : IOCoins 𝕂′) (liftRec (L := 𝕂′) (keyX (K := K) 8 r eT))

theorem pf_readsOff (eT : Env (ZMod p)) (r : List RE) : ReadsOff InhabJ8Good.c12 (pf (K := K) δ eT r) := fun χ χ' h => by
  simp only [pf, γH_readsOff δ χ χ' h]

/-- The activity sum of a slot at the row. -/
def Sa (S : SlotX (ZMod p)) (eT : Env (ZMod p)) : ZMod p := (S.ents.map fun x => x.act.eval eT).sum

/-- The affine remainder `X(χ) = Σ a_x · c_x(χ)` of a slot's denominator. -/
def Xs (S : SlotX (ZMod p)) (eT : Env (ZMod p)) (χ : Coins frameJ8 K) : 𝕂′ :=
  (S.ents.map fun x => algebraMap (ZMod p) 𝕂′ (x.act.eval eT) * pf δ eT x.rcd χ).sum

theorem Xs_readsOff (S : SlotX (ZMod p)) (eT : Env (ZMod p)) : ReadsOff InhabJ8Good.c12 (Xs δ S eT (K := K)) :=
  fun χ χ' h => by
    unfold Xs
    exact congrArg List.sum (List.map_congr_left fun x _ => by rw [pf_readsOff (K := K) δ eT x.rcd χ χ' h])

/-- **The pole events of a slot at a row**: the affine pole `ρH′ = −X/Sa`, and the two pair denominators. -/
def slotPoles (S : SlotX (ZMod p)) (eT : Env (ZMod p)) : List (BadSpec K) :=
  quadPole δ InhabJ8Good.c12 (fun χ => Xs δ S eT χ / algebraMap (ZMod p) 𝕂′ (Sa S eT)) ::
  (match S.pair with
   | some (_, a, b', _) => [quadPole δ InhabJ8Good.c12 (pf δ eT a), quadPole δ InhabJ8Good.c12 (pf δ eT b')]
   | none => [])

theorem slotPoles_OK (S : SlotX (ZMod p)) (eT : Env (ZMod p)) : ∀ s ∈ slotPoles δ S eT (K := K), s.OK := by
  intro s hs
  simp only [slotPoles, List.mem_cons] at hs
  rcases hs with rfl | hs
  · refine quadPole_OK δ _ _ fun χ χ' h => ?_
    simp only [Xs_readsOff δ S eT χ χ' h]
  · cases hp : S.pair with
    | none => simp [hp] at hs
    | some q =>
      obtain ⟨fl, a, b', _⟩ := q
      simp only [hp, List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl | rfl <;> exact quadPole_OK δ _ _ (pf_readsOff (K := K) δ eT _)

theorem lift_ne_zero {a : ZMod p} (h : a ≠ 0) : algebraMap (ZMod p) 𝕂′ a ≠ 0 :=
  fun h0 => h ((algebraMap (ZMod p) 𝕂′).injective (by rw [h0, map_zero]))

/-- **A slot's denominator is covered**: outside the slot's pole events, the slot is inactive (`A = 0`) or its
denominator `D` is non-zero.  Hypotheses: the activities read only the row (`hacts`), the records fit the width
(`hlen`), and the pair flag excludes every entry (`hex`). -/
theorem slot_cover (S : SlotX (ZMod p)) (eT e : Env (ZMod p)) (χ : Coins frameJ8 K)
    (hch : e.chal = chalVJ8 b χ) (htr : e.trace = eT.trace)
    (hacts : ∀ x ∈ S.ents, okC okFs x.act = true)
    (hlen : ∀ x ∈ S.ents, x.rcd.length ≤ 8)
    (hlenp : ∀ fl a b' bb, S.pair = some (fl, a, b', bb) → a.length ≤ 8 ∧ b'.length ≤ 8)
    (hex : ∀ fl a b' bb, S.pair = some (fl, a, b', bb) → eT.trace fl ≠ 0 → ∀ x ∈ S.ents, x.act.eval eT = 0)
    (hgood : ∀ s ∈ slotPoles δ S eT (K := K), χ ∉ s.ev) :
    aVal b δ S e = 0 ∨ dVal b δ S e ≠ 0 := by
  have hρ := ρH_re δ χ
  have hact : ∀ x ∈ S.ents, x.act.eval e = x.act.eval eT := fun x hx =>
    eval_okC okFs _ (hacts x hx) e eT (fun k i hk => by
      cases k <;> simp [okFs] at hk
      show e.trace i = eT.trace i
      rw [htr])
  have hpole0 : ρH δ χ + Xs δ S eT χ / algebraMap (ZMod p) 𝕂′ (Sa S eT) ≠ 0 :=
    quadPole_ne δ InhabJ8Good.c12 (fun χ => Xs δ S eT χ / algebraMap (ZMod p) 𝕂′ (Sa S eT)) χ _ hρ (hgood _ (by simp [slotPoles]))
  have hsum : (S.ents.map fun x => algebraMap (ZMod p) 𝕂′ (x.act.eval e) *
        Nock.NockVMROM.Thm54.VclL.Handle.TeleCQX.DX δ (gatherEnv b e) e x.rcd).sum =
      algebraMap (ZMod p) 𝕂′ (Sa S eT) * ρH δ χ + Xs δ S eT χ := by
    have : ∀ x ∈ S.ents, algebraMap (ZMod p) 𝕂′ (x.act.eval e) *
        Nock.NockVMROM.Thm54.VclL.Handle.TeleCQX.DX δ (gatherEnv b e) e x.rcd =
        algebraMap (ZMod p) 𝕂′ (x.act.eval eT) * (ρH δ χ + pf δ eT x.rcd χ) := by
      intro x hx
      rw [hact x hx, den_split δ b e χ hch x.rcd (hlen x hx), pf, keyX_congr e eT htr]
    rw [List.map_congr_left this, sum_aff]; rfl
  have hA : algebraMap (ZMod p) 𝕂′ ((S.ents.map fun x => x.act.eval e).sum) =
      algebraMap (ZMod p) 𝕂′ (Sa S eT) := by
    congr 1; unfold Sa; congr 1; exact List.map_congr_left hact
  rw [dVal_expand, aVal_expand, hsum, hA]
  -- the affine case
  have affine : (algebraMap (ZMod p) 𝕂′ (Sa S eT) = 0 ∨
      algebraMap (ZMod p) 𝕂′ (Sa S eT) * ρH δ χ + Xs δ S eT χ ≠ 0) := by
    by_cases h0 : Sa S eT = 0
    · left; rw [h0, map_zero]
    · right
      have hl := lift_ne_zero (δ := δ) (K := K) h0
      have : algebraMap (ZMod p) 𝕂′ (Sa S eT) * ρH δ χ + Xs δ S eT χ =
          algebraMap (ZMod p) 𝕂′ (Sa S eT) * (ρH δ χ + Xs δ S eT χ / algebraMap (ZMod p) 𝕂′ (Sa S eT)) := by
        field_simp
      rw [this]; exact mul_ne_zero hl hpole0
  rcases hp : S.pair with _ | ⟨fl, a, b', bb⟩
  · simp only [add_zero]
    rcases affine with h | h
    · left; exact h
    · right; exact h
  · obtain ⟨ha, hb⟩ := hlenp fl a b' bb hp
    by_cases hfl : eT.trace fl = 0
    · have : e.trace fl = 0 := by rw [htr]; exact hfl
      simp only [this, map_zero, zero_mul, add_zero]
      rcases affine with h | h
      · left; exact h
      · right; exact h
    · have h0 := hex fl a b' bb hp hfl
      have hS : Sa S eT = 0 := by unfold Sa; rw [List.map_congr_left h0]; simp
      have hX : Xs δ S eT χ = 0 := by
        unfold Xs; rw [List.map_congr_left (fun x hx => by rw [h0 x hx, map_zero, zero_mul])]; simp
      have hfe : e.trace fl ≠ 0 := by rw [htr]; exact hfl
      right
      dsimp only
      rw [hS, hX, map_zero, zero_mul, zero_add, zero_add, den_split δ b e χ hch a ha, den_split δ b e χ hch b' hb]
      have hpa : ρH δ χ + pf δ eT a χ ≠ 0 := quadPole_ne δ InhabJ8Good.c12 (pf δ eT a) χ _ hρ (hgood _ (by simp [slotPoles, hp]))
      have hpb : ρH δ χ + pf δ eT b' χ ≠ 0 := quadPole_ne δ InhabJ8Good.c12 (pf δ eT b') χ _ hρ (hgood _ (by simp [slotPoles, hp]))
      refine mul_ne_zero (lift_ne_zero (δ := δ) (K := K) hfe) (mul_ne_zero ?_ ?_)
      · rw [pf, keyX_congr e eT htr] at *; exact hpa
      · rw [pf, keyX_congr e eT htr] at *; exact hpb

end Gen

section Rows
variable {p : ℕ} [Fact p.Prime]
open Nock.NockVMROM.Thm54.VclL.Handle.RowDecodeVSX (stIdx)
open Nock.NockVMROM.Thm54.VclL.Handle.HonestCompX (colX cPr cPr2 isPair)

theorem hacts_slots {F : Type} [Field F] : ∀ S ∈ Nock.NockVMROM.Thm54.VclL.Handle.ChipHX.slotsX (F := F),
    ∀ x ∈ S.ents, okC okFs x.act = true := by
  have h : (Nock.NockVMROM.Thm54.VclL.Handle.ChipHX.slotsX (F := F)).all
      (fun S => S.ents.all fun x => okC okFs x.act) = true := by rfl
  intro S hS x hx
  exact List.all_eq_true.mp (List.all_eq_true.mp h S hS) x hx

theorem hlen_slots {F : Type} [Field F] : ∀ S ∈ Nock.NockVMROM.Thm54.VclL.Handle.ChipHX.slotsX (F := F),
    (∀ x ∈ S.ents, x.rcd.length ≤ 8) ∧
    ∀ fl a b' bb, S.pair = some (fl, a, b', bb) → a.length ≤ 8 ∧ b'.length ≤ 8 := by
  have h : (Nock.NockVMROM.Thm54.VclL.Handle.ChipHX.slotsX (F := F)).all
      (fun S => (S.ents.all fun x => decide (x.rcd.length ≤ 8)) &&
        (match S.pair with
         | some (_, a, b', _) => decide (a.length ≤ 8) && decide (b'.length ≤ 8)
         | none => true)) = true := by rfl
  intro S hS
  have h1 := List.all_eq_true.mp h S hS
  simp only [Bool.and_eq_true] at h1
  refine ⟨fun x hx => by simpa using List.all_eq_true.mp h1.1 x hx, fun fl a b' bb hp => ?_⟩
  have := h1.2
  rw [hp] at this
  simpa using this

/-- A state-selected activity vanishes when the row's state is not in its state list. -/
theorem act_zero (x : EntX (ZMod p)) (eT : Env (ZMod p)) (H : Noun → ℕ × ℕ) (pd : RowNX → ℕ × (ℕ × ℕ) × (ℕ × ℕ))
    (r : RowNX) (fst lst : ZMod p) (hT : eT.trace = colX H pd r fst lst)
    (hs : ∀ k ∈ x.states, k < 17 ∧ stIdx r.st ≠ k) : x.act.eval eT = 0 := by
  have : (selS (F := ZMod p) x.states).eval eT = 0 := by
    unfold selS
    rw [CoeffExpr.eval_sumList]
    refine List.sum_eq_zero fun v hv => ?_
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hv
    obtain ⟨h17, hne⟩ := hs k hk
    simp [cc, CoeffExpr.eval, hT, colX, h17, hne]
  simp [EntX.act, CoeffExpr.eval, this]

theorem hex_slots (S : SlotX (ZMod p)) (hS : S ∈ Nock.NockVMROM.Thm54.VclL.Handle.ChipHX.slotsX (F := ZMod p)) (eT : Env (ZMod p))
    (H : Noun → ℕ × ℕ) (pd : RowNX → ℕ × (ℕ × ℕ) × (ℕ × ℕ)) (r : RowNX) (fst lst : ZMod p)
    (hT : eT.trace = colX H pd r fst lst) :
    ∀ fl a b' bb, S.pair = some (fl, a, b', bb) → eT.trace fl ≠ 0 → ∀ x ∈ S.ents, x.act.eval eT = 0 := by
  intro fl a b' bb hp hfl x hx
  simp only [Nock.NockVMROM.Thm54.VclL.Handle.ChipHX.slotsX, List.mem_cons, List.not_mem_nil, or_false] at hS
  rcases hS with rfl | rfl | rfl | rfl
  · simp [slot0X] at hp
  · simp [slot1X] at hp
  · -- slot 2: flag column `prX = 24`
    simp only [slot2X, Option.some.injEq, Prod.mk.injEq] at hp
    obtain ⟨rfl, -⟩ := hp
    have hst : stIdx r.st = 5 ∨ stIdx r.st = 12 := by
      rw [hT] at hfl
      simp only [colX, prX] at hfl
      revert hfl
      simp only [show (24 : ℕ) < 17 ↔ False by decide, if_false, show (24 : ℕ) ≠ 17 from by decide,
        show (24 : ℕ) ≠ 18 from by decide, show (24 : ℕ) ≠ 19 from by decide, show (24 : ℕ) ≠ 20 from by decide,
        show (24 : ℕ) ≠ 21 from by decide, show (24 : ℕ) ≠ 22 from by decide, show (24 : ℕ) ≠ 23 from by decide,
        if_true]
      unfold cPr
      cases r.st <;> simp [stIdx]
    refine act_zero x eT H pd r fst lst hT fun k hk => ?_
    simp only [slot2X, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [l3X, consCol] at hk <;> omega
  · simp only [slot3X, Option.some.injEq, Prod.mk.injEq] at hp
    obtain ⟨rfl, -⟩ := hp
    have hst : stIdx r.st = 5 := by
      have h64 : colX H pd r fst lst 64 = cPr2 H r := by simp [colX]
      rw [hT] at hfl
      change colX H pd r fst lst 64 ≠ 0 at hfl
      rw [h64] at hfl
      by_contra hne
      have hnp : ¬ isPair H r := fun hp => hne (by rw [hp.1]; rfl)
      simp [cPr2, hnp] at hfl
    refine act_zero x eT H pd r fst lst hT fun k hk => ?_
    simp only [slot3X, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl <;> simp [sS10, sS11j] at hk <;> omega
end Rows
section Compute
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

/-- The four compute slots. -/
abbrev SLOTS : List (SlotX (ZMod p)) := Nock.NockVMROM.Thm54.VclL.Handle.ChipHX.slotsX (F := ZMod p)

/-- The coin-free row environment of the honest compute trace. -/
def envT (H : Noun → ℕ × ℕ) (pd : RowNX → ℕ × (ℕ × ℕ) × (ℕ × ℕ)) (W : List (NTree SkelX)) (j : ℕ) : Env (ZMod p) :=
  env0 H pd W (fun _ => 0) (fun _ => 0) j

/-- **The compute chip's pole events**: for every row `j < n` and every slot, the slot's pole events. -/
def compPoles (H : Noun → ℕ × ℕ) (pd : RowNX → ℕ × (ℕ × ℕ) × (ℕ × ℕ)) (W : List (NTree SkelX)) (n : ℕ) :
    List (BadSpec K) :=
  (List.range n).flatMap fun j => (SLOTS (p := p)).flatMap fun S => slotPoles δ S (envT H pd W j)

theorem compPoles_OK (H : Noun → ℕ × ℕ) (pd : RowNX → ℕ × (ℕ × ℕ) × (ℕ × ℕ)) (W : List (NTree SkelX)) (n : ℕ) :
    ∀ s ∈ compPoles (K := K) δ H pd W n, s.OK := by
  intro s hs
  simp only [compPoles, List.mem_flatMap] at hs
  obtain ⟨j, -, S, -, hs⟩ := hs
  exact slotPoles_OK δ S _ s hs

theorem cost_slotPoles (S : SlotX (ZMod p)) (eT : Env (ZMod p)) :
    costL (slotPoles (K := K) δ S eT) ≤ 3 := by
  unfold slotPoles
  cases S.pair with
  | none => simp [costL, quadPole, BadSpec.cost]
  | some q => obtain ⟨fl, a, b', _⟩ := q; simp [costL, quadPole, BadSpec.cost]

theorem costL_flatMap {α : Type} (l : List α) (f : α → List (BadSpec K)) (m : ℕ)
    (h : ∀ x ∈ l, costL (f x) ≤ m) : costL (l.flatMap f) ≤ l.length * m := by
  induction l with
  | nil => simp [costL]
  | cons x l ih =>
    have h1 := h x (by simp)
    have h2 := ih fun y hy => h y (by simp [hy])
    simp only [List.flatMap_cons, costL, List.map_append, List.sum_append, List.length_cons] at h1 h2 ⊢
    nlinarith

/-- **Cost of the compute pole events**: at most `12 n` pins. -/
theorem cost_compPoles (H : Noun → ℕ × ℕ) (pd : RowNX → ℕ × (ℕ × ℕ) × (ℕ × ℕ)) (W : List (NTree SkelX)) (n : ℕ) :
    costL (compPoles (K := K) δ H pd W n) ≤ 12 * n := by
  unfold compPoles
  have h := costL_flatMap (K := K) (List.range n) (fun j => (SLOTS (p := p)).flatMap fun S => slotPoles δ S (envT H pd W j)) 12
    (fun j _ => by
      have := costL_flatMap (K := K) (SLOTS (p := p)) (fun S => slotPoles δ S (envT H pd W j)) 3
        (fun S _ => cost_slotPoles δ S _)
      have hl : (SLOTS (p := p)).length = 4 := rfl
      omega)
  simpa [mul_comm] using h

/-- **`DenCovered` for the compute chip (pointwise form)**: at any coin outside every event of `compPoles`, every
slot of every row is inactive or has a non-zero denominator (any public vector). -/
theorem compDen_ok (H : Noun → ℕ × ℕ) (pd : RowNX → ℕ × (ℕ × ℕ) × (ℕ × ℕ)) (W : List (NTree SkelX)) (n : ℕ)
    (pub : ℕ → ZMod p) (χ : Coins frameJ8 K) (hg : ∀ s ∈ compPoles (K := K) δ H pd W n, χ ∉ s.ev) :
    ∀ j < n, ∀ S ∈ (SLOTS (p := p)),
      aVal b δ S (env0 H pd W (chalVJ8 b χ) pub j) = 0 ∨ dVal b δ S (env0 H pd W (chalVJ8 b χ) pub j) ≠ 0 := by
  intro j hj S hS
  refine slot_cover δ b S (envT H pd W j) _ χ rfl rfl (hacts_slots S hS) (hlen_slots S hS).1
    (hlen_slots S hS).2 ?_ ?_
  · exact hex_slots S hS _ H pd (rowAtWX W (j + 1)) (flX j) (llX W j) rfl
  · intro s hs
    exact hg s (by
      simp only [compPoles, List.mem_flatMap]
      exact ⟨j, List.mem_range.mpr hj, S, hS, hs⟩)

open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8 in
/-- **L5's `DenCovered` for the compute chip**: any bad list `L` containing `compPoles` covers the slots. -/
theorem denCovered_of_sub {Rg : Nock.Jet.VerifiedRegistry} {fuel : ℕ} {s f r : Noun}
    (B : HonestJ8 p K δ Rg fuel s f r) (L : List (BadSpec K))
    (hsub : ∀ s ∈ compPoles (K := K) δ B.H B.pd B.W B.Pb.n, s ∈ L) (hn : 0 < B.Pb.n) :
    DenCovered δ b B L := by
  intro χ j hj S hS
  by_cases hg : ∀ e ∈ L, χ ∉ e.ev
  · rcases compDen_ok δ b B.H B.pd B.W B.Pb.n (pubJ δ b B χ) χ (fun s hs => hg s (hsub s hs)) j hj S hS with h | h
    · exact Or.inl h
    · right
      obtain ⟨e0, he0⟩ : ∃ e0, e0 ∈ compPoles (K := K) δ B.H B.pd B.W B.Pb.n := by
        have hne : (compPoles (K := K) δ B.H B.pd B.W B.Pb.n) ≠ [] := by
          simp only [compPoles, ne_eq, List.flatMap_eq_nil_iff, not_forall]
          refine ⟨0, List.mem_range.mpr hn, ?_⟩
          simp [Nock.NockVMROM.Thm54.VclL.Handle.ChipHX.slotsX, slotPoles]
        exact List.exists_mem_of_ne_nil _ hne
      exact ⟨e0, hsub _ he0, fun _ => h⟩
  · simp only [not_forall, not_not] at hg
    obtain ⟨e, he, hχ⟩ := hg
    exact Or.inr ⟨e, he, fun h => absurd hχ h⟩
end Compute

end
end Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8CompPole
