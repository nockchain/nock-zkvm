/-
  Nock/NockVMROM/Thm54/VclL/Handle/J9A/ComplJ9AOfComp.lean

* Generic: `accV9_pub` (the twin accumulator totals read no public), `slot_cover9` (J-8's `slot_cover` with the
    activity agreement as a hypothesis), the twin slot facts `hacts9` / `hlen9` / `hex9`, and `compDen9_ok` (twin of
    `ComplJ8CompPole.compDen_ok`: outside `compPoles9` every twin slot is inactive or has a non-zero denominator).
  * At the run (`BRun9A`): `hpair9A` (from `hop5` alone: only `s5` rows are pairs), the publics `hpubA` / `hpSA` /
    `hρA` (twins of J-9 B's `hpub9` / `hpS9` / `hρ9`), `hnbA`, `hordA`, and the fields `hsatXA`, `hinjXA`,
    `hadjXA`.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.ComplJ9ARun
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.HonestSatX9
import Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9BComp
import Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Atom

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AOfComp

open Nock Nock.Noun Nock.Walk Nock.Edit Nock.Edit.GenX Nock.Reified Nock.Framework Module Polynomial
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler
open Nock.NockVMROM.Thm54.T0Tower Nock.NockVMROM.Thm54.T0TowerFP Nock.NockVMROM.Thm54.StrictExtension
open Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.VclL.Compute.LogUp Nock.NockVMROM.Thm54.VclL.Compute.TowerD
open Nock.NockVMROM.Thm54.VclL.Handle.ChipH (cc notC selS consCol)
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHX Nock.NockVMROM.Thm54.VclL.Handle.ChipHX9
open Nock.NockVMROM.Thm54.VclL.Handle.HonestSlotX
open Nock.NockVMROM.Thm54.VclL.Handle.HonestCompX (colX cPr cPr2 isPair)
open Nock.NockVMROM.Thm54.VclL.HonestTraceX (okC eval_okC)
open Nock.NockVMROM.Thm54.VclL.HonestTraceX9 (okFs9 env0 env1 preT9 invV9 invCol9 accV9 baseT9)
open Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8 (frameJ8 toVSQ)
open Nock.NockVMROM.Thm54.VclL.Handle.VerJ8
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Bad
open Nock.NockVMROM.Thm54.VclL.Handle.DenXJ8
open Nock.NockVMROM.Thm54.FiniteIO Nock.NockVMROM.Thm54.SVFrame
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AGen (LX9)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ACompRow (colX9 colS0B colS10B colS10S)

noncomputable section

/-! ## 1. The twin accumulator totals read no public -/

section Acc
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [Fintype K] [DecidableEq F]
  (b : Basis (Fin 3) F K) (δ : F) [Fact (¬ IsSquare (algebraMap F K δ))]
  (H : Noun → ℕ × ℕ) (pd : RowNX → ℕ × (ℕ × ℕ) × (ℕ × ℕ)) (idOf : ℕ → ℕ) (W : List (NTree LX9))

theorem invV9_pub (chalV pub1 pub2 : ℕ → F) (j : ℕ) (S : SlotX F) (hS : S ∈ slotsX9 (F := F)) :
    invV9 b δ H pd idOf W chalV pub1 j S = invV9 b δ H pd idOf W chalV pub2 j S := by
  have h := HonestTraceX9.dVal_aVal_congr9 b δ hS (env0 H pd idOf W chalV pub1 j) (env0 H pd idOf W chalV pub2 j)
    (fun c _ => rfl) rfl
  unfold invV9; rw [h.1, h.2]

theorem slotAt9_mem (i : ℕ) : HonestTraceX9.slotAt9 (F := F) i ∈ slotsX9 (F := F) := by
  unfold HonestTraceX9.slotAt9
  split <;> simp [slotsX9]

theorem preT9_pub (chalV pub1 pub2 : ℕ → F) (j c : ℕ) :
    preT9 b δ H pd idOf W chalV pub1 j c = preT9 b δ H pd idOf W chalV pub2 j c := by
  unfold preT9 invCol9
  rw [invV9_pub b δ H pd idOf W chalV pub1 pub2 j _ (slotAt9_mem _)]

/-- **`accV9_pub`**: the twin accumulator totals do not read the publics (twin of `InhabJ8Comp.accV_pub`). -/
theorem accV9_pub (chalV pub1 pub2 : ℕ → F) (a i : ℕ) :
    accV9 b δ H pd idOf W chalV pub1 a i = accV9 b δ H pd idOf W chalV pub2 a i := by
  unfold accV9
  refine Finset.sum_congr rfl fun j _ => ?_
  exact HonestTraceX9.termVal_congr9 b _ _ _ _ fun c _ => preT9_pub b δ H pd idOf W chalV pub1 pub2 j c

end Acc

/-! ## 2. The twin slots: activities, record lengths, the pair flag -/

section Slots

theorem hacts9 {F : Type} [Field F] : ∀ S ∈ slotsX9 (F := F), ∀ x ∈ S.ents, okC okFs9 x.act = true := by
  have h : (slotsX9 (F := F)).all (fun S => S.ents.all fun x => okC okFs9 x.act) = true := by rfl
  intro S hS x hx
  exact List.all_eq_true.mp (List.all_eq_true.mp h S hS) x hx

theorem hlen9 {F : Type} [Field F] : ∀ S ∈ slotsX9 (F := F),
    (∀ x ∈ S.ents, x.rcd.length ≤ 8) ∧
    ∀ fl a b' bb, S.pair = some (fl, a, b', bb) → a.length ≤ 8 ∧ b'.length ≤ 8 := by
  have h : (slotsX9 (F := F)).all
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

theorem states2_lt {F : Type} [Field F] : ∀ x ∈ (slot2X (F := F)).ents, ∀ k ∈ x.states, k < 17 := by
  have h : (slot2X (F := F)).ents.all (fun x => x.states.all fun k => decide (k < 17)) = true := by rfl
  intro x hx k hk
  simpa using List.all_eq_true.mp (List.all_eq_true.mp h x hx) k hk

theorem states3_lt {F : Type} [Field F] : ∀ x ∈ (slot3X (F := F)).ents, ∀ k ∈ x.states, k < 17 := by
  have h : (slot3X (F := F)).ents.all (fun x => x.states.all fun k => decide (k < 17)) = true := by rfl
  intro x hx k hk
  simpa using List.all_eq_true.mp (List.all_eq_true.mp h x hx) k hk

/-- A state-selected activity vanishes when every selected state column is `0`. -/
theorem act_zero9 {F : Type} [Field F] (x : EntX F) (eT : Env F) (hs : ∀ k ∈ x.states, eT.trace k = 0) :
    x.act.eval eT = 0 := by
  have : (selS (F := F) x.states).eval eT = 0 := by
    unfold selS
    rw [CoeffExpr.eval_sumList]
    refine List.sum_eq_zero fun v hv => ?_
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hv
    simp [cc, CoeffExpr.eval, hs k hk]
  simp [EntX.act, CoeffExpr.eval, this]

section Cols
variable {F : Type} [Field F] (H : Noun → ℕ × ℕ) (pd : RowNX → ℕ × (ℕ × ℕ) × (ℕ × ℕ)) (idOf : ℕ → ℕ)

theorem colX9_lt17 (l : LX9) (fst lst : F) (h : l.chip ≠ .old) (k : ℕ) (hk : k < 17) :
    colX9 H pd idOf l fst lst k = 0 := by
  cases hc : l.chip with
  | old => exact absurd hc h
  | s0B => simp [colX9, hc, colS0B, hk]
  | s10B => simp [colX9, hc, colS10B, hk]
  | s10S => simp [colX9, hc, colS10S, hk]

theorem colX9_124 (l : LX9) (fst lst : F) (h : l.chip ≠ .s10B) : colX9 H pd idOf l fst lst 124 = 0 := by
  cases hc : l.chip with
  | old => simp only [colX9, hc]; exact ComplJ9ACompRow.colX_ge69 H pd l.rn fst lst 124 (by norm_num)
  | s0B => simp [colX9, hc, colS0B]
  | s10B => exact absurd hc h
  | s10S => simp [colX9, hc, colS10S]

theorem colX9_125 (l : LX9) (fst lst : F) (h : l.chip ≠ .s10S) : colX9 H pd idOf l fst lst 125 = 0 := by
  cases hc : l.chip with
  | old => simp only [colX9, hc]; exact ComplJ9ACompRow.colX_ge69 H pd l.rn fst lst 125 (by norm_num)
  | s0B => simp [colX9, hc, colS0B]
  | s10B => simp [colX9, hc, colS10B]
  | s10S => exact absurd hc h

theorem colX9_24_s10B (l : LX9) (fst lst : F) (hc : l.chip = .s10B) (hst : l.rn.st = .s10) :
    colX9 H pd idOf l fst lst prX = 0 := by
  simp [colX9, hc, colS10B, prX, colX, cPr, hst]

theorem colX9_64 (l : LX9) (fst lst : F) (hc : l.chip = .s10B ∨ l.chip = .s10S)
    (hst : l.chip = .s10B → l.rn.st = .s10) : colX9 H pd idOf l fst lst 64 = 0 := by
  rcases hc with hc | hc
  · have hnp : ¬ isPair H l.rn := fun hp => by have := hp.1; rw [hst hc] at this; cases this
    simp [colX9, hc, colS10B, colX, cPr2, hnp]
  · simp [colX9, hc, colS10S]

end Cols

section Hex
variable {p : ℕ} [Fact p.Prime] (H : Noun → ℕ × ℕ) (pd : RowNX → ℕ × (ℕ × ℕ) × (ℕ × ℕ)) (idOf : ℕ → ℕ)

/-- **The pair flag excludes every entry** (twin of `ComplJ8CompPole.hex_slots`, at the J-9 A columns; the one row
fact used: an `s10B` row is an op-10 row). -/
theorem hex9 (S : SlotX (ZMod p)) (hS : S ∈ slotsX9 (F := ZMod p)) (eT : Env (ZMod p)) (l : LX9) (fst lst : ZMod p)
    (hT : eT.trace = colX9 H pd idOf l fst lst) (hl : l.chip = .s10B → l.rn.st = .s10) :
    ∀ fl a b' bb, S.pair = some (fl, a, b', bb) → eT.trace fl ≠ 0 → ∀ x ∈ S.ents, x.act.eval eT = 0 := by
  intro fl a b' bb hp hfl x hx
  simp only [slotsX9, List.mem_cons, List.not_mem_nil, or_false] at hS
  rcases hS with rfl | rfl | rfl | rfl
  · simp [slot0X9, extSlot, slot0X] at hp
  · simp [slot1X9, extSlot, slot1X] at hp
  · have hp0 : (slot2X (F := ZMod p)).pair = some (fl, a, b', bb) := hp
    simp only [slot2X9, extSlot, List.mem_append] at hx
    rcases hx with hx | hx
    · by_cases hc : l.chip = .old
      · have hT' : eT.trace = colX H pd l.rn fst lst := by
          rw [hT, ComplJ9ACompRow.colX9_old H pd idOf l fst lst hc]
        exact ComplJ8CompPole.hex_slots slot2X
          (show slot2X ∈ [slot0X, slot1X, slot2X, slot3X] from
            List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)) eT H pd l.rn fst lst hT' fl a b' bb hp0 hfl x hx
      · exact act_zero9 x eT fun k hk => by rw [hT]; exact colX9_lt17 H pd idOf l fst lst hc k (states2_lt x hx k hk)
    · simp only [ents2New, List.mem_cons, List.not_mem_nil, or_false] at hx
      subst hx
      refine act_zero9 _ eT fun k hk => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      subst hk
      by_cases hc : l.chip = .s10B
      · simp only [slot2X, Option.some.injEq, Prod.mk.injEq] at hp0
        obtain ⟨rfl, -⟩ := hp0
        exact absurd (by rw [hT]; exact colX9_24_s10B H pd idOf l fst lst hc (hl hc)) hfl
      · rw [hT]; exact colX9_124 H pd idOf l fst lst hc
  · have hp0 : (slot3X (F := ZMod p)).pair = some (fl, a, b', bb) := hp
    simp only [slot3X, Option.some.injEq, Prod.mk.injEq] at hp0
    obtain ⟨rfl, -⟩ := hp0
    simp only [slot3X9, extSlot, List.mem_append] at hx
    rcases hx with hx | hx
    · by_cases hc : l.chip = .old
      · have hT' : eT.trace = colX H pd l.rn fst lst := by
          rw [hT, ComplJ9ACompRow.colX9_old H pd idOf l fst lst hc]
        exact ComplJ8CompPole.hex_slots slot3X
          (show slot3X ∈ [slot0X, slot1X, slot2X, slot3X] from
            List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))) eT H pd l.rn fst lst hT' _ _ _ _ rfl hfl x hx
      · exact act_zero9 x eT fun k hk => by rw [hT]; exact colX9_lt17 H pd idOf l fst lst hc k (states3_lt x hx k hk)
    · simp only [ents3New, List.mem_cons, List.not_mem_nil, or_false] at hx
      have h64 : l.chip = .s10B ∨ l.chip = .s10S → False := fun hc =>
        hfl (by rw [hT]; exact colX9_64 H pd idOf l fst lst hc hl)
      rcases hx with rfl | rfl
      · refine act_zero9 _ eT fun k hk => ?_
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
        subst hk
        rw [hT]; exact colX9_124 H pd idOf l fst lst fun hc => h64 (Or.inl hc)
      · refine act_zero9 _ eT fun k hk => ?_
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
        subst hk
        rw [hT]; exact colX9_125 H pd idOf l fst lst fun hc => h64 (Or.inr hc)

end Hex
end Slots

/-! ## 3. The slot-pole cover (twin of `ComplJ8CompPole.slot_cover` / `compDen_ok`) -/

section Cover
open Nock.NockVMROM.Thm54.VclL.HonestWalkX9 (rowAt9 fl1 llW)
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

/-- **A slot's denominator is covered** (J-8's `slot_cover`, with the activity agreement `hact` as the hypothesis in
place of J-8's read-set `okFs`: the twin activities read the round-0 columns `okFs9`). -/
theorem slot_cover9 (S : SlotX (ZMod p)) (eT e : Env (ZMod p)) (χ : Coins frameJ8 K)
    (hch : e.chal = chalVJ8 b χ) (htr : e.trace = eT.trace)
    (hact : ∀ x ∈ S.ents, x.act.eval e = x.act.eval eT)
    (hlen : ∀ x ∈ S.ents, x.rcd.length ≤ 8)
    (hlenp : ∀ fl a b' bb, S.pair = some (fl, a, b', bb) → a.length ≤ 8 ∧ b'.length ≤ 8)
    (hex : ∀ fl a b' bb, S.pair = some (fl, a, b', bb) → eT.trace fl ≠ 0 → ∀ x ∈ S.ents, x.act.eval eT = 0)
    (hgood : ∀ s ∈ ComplJ8CompPole.slotPoles δ S eT (K := K), χ ∉ s.ev) :
    aVal b δ S e = 0 ∨ dVal b δ S e ≠ 0 := by
  have hρ := ρH_re δ χ
  have hpole0 : ρH δ χ + ComplJ8CompPole.Xs δ S eT χ / algebraMap (ZMod p) 𝕂′ (ComplJ8CompPole.Sa S eT) ≠ 0 :=
    quadPole_ne δ InhabJ8Good.c12 (fun χ => ComplJ8CompPole.Xs δ S eT χ /
      algebraMap (ZMod p) 𝕂′ (ComplJ8CompPole.Sa S eT)) χ _ hρ
      (hgood _ (by simp [ComplJ8CompPole.slotPoles]))
  have hsum : (S.ents.map fun x => algebraMap (ZMod p) 𝕂′ (x.act.eval e) *
        Nock.NockVMROM.Thm54.VclL.Handle.TeleCQX.DX δ (gatherEnv b e) e x.rcd).sum =
      algebraMap (ZMod p) 𝕂′ (ComplJ8CompPole.Sa S eT) * ρH δ χ + ComplJ8CompPole.Xs δ S eT χ := by
    have : ∀ x ∈ S.ents, algebraMap (ZMod p) 𝕂′ (x.act.eval e) *
        Nock.NockVMROM.Thm54.VclL.Handle.TeleCQX.DX δ (gatherEnv b e) e x.rcd =
        algebraMap (ZMod p) 𝕂′ (x.act.eval eT) * (ρH δ χ + ComplJ8CompPole.pf δ eT x.rcd χ) := by
      intro x hx
      rw [hact x hx, ComplJ8CompPole.den_split δ b e χ hch x.rcd (hlen x hx), ComplJ8CompPole.pf,
        ComplJ8CompPole.keyX_congr e eT htr]
    rw [List.map_congr_left this, ComplJ8CompPole.sum_aff]; rfl
  have hA : algebraMap (ZMod p) 𝕂′ ((S.ents.map fun x => x.act.eval e).sum) =
      algebraMap (ZMod p) 𝕂′ (ComplJ8CompPole.Sa S eT) := by
    congr 1; unfold ComplJ8CompPole.Sa; congr 1; exact List.map_congr_left hact
  rw [ComplJ8CompPole.dVal_expand, ComplJ8CompPole.aVal_expand, hsum, hA]
  have affine : (algebraMap (ZMod p) 𝕂′ (ComplJ8CompPole.Sa S eT) = 0 ∨
      algebraMap (ZMod p) 𝕂′ (ComplJ8CompPole.Sa S eT) * ρH δ χ + ComplJ8CompPole.Xs δ S eT χ ≠ 0) := by
    by_cases h0 : ComplJ8CompPole.Sa S eT = 0
    · left; rw [h0, map_zero]
    · right
      have hl := ComplJ8CompPole.lift_ne_zero (δ := δ) (K := K) h0
      have : algebraMap (ZMod p) 𝕂′ (ComplJ8CompPole.Sa S eT) * ρH δ χ + ComplJ8CompPole.Xs δ S eT χ =
          algebraMap (ZMod p) 𝕂′ (ComplJ8CompPole.Sa S eT) * (ρH δ χ + ComplJ8CompPole.Xs δ S eT χ /
            algebraMap (ZMod p) 𝕂′ (ComplJ8CompPole.Sa S eT)) := by
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
      have hS : ComplJ8CompPole.Sa S eT = 0 := by
        unfold ComplJ8CompPole.Sa; rw [List.map_congr_left h0]; simp
      have hX : ComplJ8CompPole.Xs δ S eT χ = 0 := by
        unfold ComplJ8CompPole.Xs; rw [List.map_congr_left (fun x hx => by rw [h0 x hx, map_zero, zero_mul])]; simp
      have hfe : e.trace fl ≠ 0 := by rw [htr]; exact hfl
      right
      dsimp only
      rw [hS, hX, map_zero, zero_mul, zero_add, zero_add, ComplJ8CompPole.den_split δ b e χ hch a ha,
        ComplJ8CompPole.den_split δ b e χ hch b' hb]
      have hpa : ρH δ χ + ComplJ8CompPole.pf δ eT a χ ≠ 0 :=
        quadPole_ne δ InhabJ8Good.c12 (ComplJ8CompPole.pf δ eT a) χ _ hρ
          (hgood _ (by simp [ComplJ8CompPole.slotPoles, hp]))
      have hpb : ρH δ χ + ComplJ8CompPole.pf δ eT b' χ ≠ 0 :=
        quadPole_ne δ InhabJ8Good.c12 (ComplJ8CompPole.pf δ eT b') χ _ hρ
          (hgood _ (by simp [ComplJ8CompPole.slotPoles, hp]))
      refine mul_ne_zero (ComplJ8CompPole.lift_ne_zero (δ := δ) (K := K) hfe) (mul_ne_zero ?_ ?_)
      · rw [ComplJ8CompPole.pf, ComplJ8CompPole.keyX_congr e eT htr] at *; exact hpa
      · rw [ComplJ8CompPole.pf, ComplJ8CompPole.keyX_congr e eT htr] at *; exact hpb

/-- **`DenCovered` for the twin compute chip (pointwise)**: outside every event of `compPoles9`, every twin slot of
every row has a non-zero denominator or is inactive (any public vector).  Row fact: `s10B` rows are op-10 rows. -/
theorem compDen9_ok (H : Noun → ℕ × ℕ) (pd : RowNX → ℕ × (ℕ × ℕ) × (ℕ × ℕ)) (idOf : ℕ → ℕ)
    (W : List (NTree LX9)) (n : ℕ) (pub : ℕ → ZMod p) (χ : Coins frameJ8 K)
    (hl : ∀ j < n, (rowAt9 W (j + 1)).chip = .s10B → (rowAt9 W (j + 1)).rn.st = .s10)
    (hg : ∀ s ∈ ComplJ9ARun.compPoles9 (K := K) δ H pd idOf W n, χ ∉ s.ev) :
    ∀ j < n, ∀ S ∈ slotsX9 (F := ZMod p),
      dVal b δ S (env0 H pd idOf W (chalVJ8 b χ) pub j) ≠ 0 ∨
        aVal b δ S (env0 H pd idOf W (chalVJ8 b χ) pub j) = 0 := by
  intro j hj S hS
  rcases slot_cover9 δ b S (env0 H pd idOf W (fun _ => 0) (fun _ => 0) j) (env0 H pd idOf W (chalVJ8 b χ) pub j) χ
      rfl rfl
      (fun x hx => eval_okC okFs9 _ (hacts9 S hS x hx) _ _ (fun k i hk => by
        cases k <;> simp only [okFs9, Bool.false_eq_true] at hk; rfl))
      (hlen9 S hS).1 (hlen9 S hS).2
      (hex9 H pd idOf S hS _ (rowAt9 W (j + 1)) (fl1 (j + 1)) (llW W (j + 1)) rfl (hl j hj))
      (fun s hs => hg s (by
        simp only [ComplJ9ARun.compPoles9, List.mem_flatMap]
        exact ⟨j, List.mem_range.mpr hj, S, hS, hs⟩)) with h | h
  exacts [Or.inr h, Or.inl h]

end Cover

/-! ## 4. `hpair` from `hop5` alone -/

section Pair
open Nock.NockVMROM.Thm54.VclL.Handle.HonestCompX (HdlOK PairOK)

/-- **`hpair` from the op-5 binder alone**: a pair row is an `s5` row, where `SmallX` is exactly `Op5RowX` (J-8's
`hpair_of_binders` reads `hax` only through `SmallX` at the other states). -/
theorem hpair9 {p : ℕ} [Fact p.Prime] {R : Nock.Jet.Registry} {fuel : ℕ} {s f r : Noun}
    {t : NTree SkelX} (hgen : genX R fuel s f = some (t, r)) {H : Noun → ℕ × ℕ}
    (hH : HdlOK (ringChar (ZMod p)) H) (hp63 : 2 ^ 63 < p) (sx : ℕ → ℕ → ℕ)
    (hop5 : ComplJ8.ProgOp5OK p t) :
    ∀ u, InTree t u → isPair H (rowOfSkelX u.label) →
      PairOK (F := ZMod p) (HonestPairX.pdX sx (rowOfSkelX u.label)) := by
  have hrc : ringChar (ZMod p) = p := ZMod.ringChar_zmod_n p
  have hB : Nock.Atoms.B ≤ ringChar (ZMod p) := by
    rw [hrc, ComplJ8Atom.B_lt]
    have : (2 : ℕ) ^ 32 ≤ 2 ^ 63 := Nat.pow_le_pow_right (by norm_num) (by norm_num)
    omega
  intro u hu hp
  refine HonestPairX.pairOK_pdX hH hB sx (HonestRowX.rowOKX_of_genX hgen hu ?_) hp
  have hst := hp.1
  rw [hrc]
  unfold HonestRowX.SmallX
  simp only [hst]
  exact hop5 u hu hst

end Pair

/-! ## 5. The compute fields at `BRun9A` -/

section Run
open Nock.NockVMROM.Thm54.VclL.HonestWalkX9 (rowAt9 fl1 llW)
open Nock.NockVMROM.Thm54.VclL.Handle.HonestCompX (HdlOK hk hv)
open Nock.NockVMROM.Thm54.VclL.Handle.HonestWalkX (hlX tripOf)
open Nock.NockVMROM.Thm54.VclL.Handle.ChipH (chalAlphaW chalGammaW pubIC pubSeed pubOut pubRhoX pubRhoP)
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHQ (pubRhoXIm pubRhoPIm)
open Nock.NockVMROM.Thm54.VclL.HonestTraceX (pubOfA)
open Nock.NockVMROM.Thm54.VclL.Handle.FrameVS Nock.NockVMROM.Thm54.VclL.Handle.FrameVSQ
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8 (cJ)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Of (powN powN_ok)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ADataRec (j9aDataOf)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AGen (genX9T)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ARun
open Nock.NockVMROM.Thm54.VclL.Handle.RealIOJ9A (qX9)
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {Rg : Nock.Jet.VerifiedRegistry} (Rt : ℕ → Nock.Jet.Autogen.Tpl) {fuel : ℕ} {s f r : Noun}
  {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r))

local notation "DA" => j9aDataOf p Rg Rt hgen

/-! ### Side facts -/

theorem p63_of (hpG : p = Nock.Atoms.p) : 2 ^ 63 < p := by rw [hpG]; simp [Nock.Atoms.p, Nock.Field.p]
theorem p62_of (hpG : p = Nock.Atoms.p) : 2 ^ 62 ≤ p := le_of_lt (lt_trans (by norm_num) (p63_of hpG))
theorem p64_of (hpG : p = Nock.Atoms.p) : p ≤ 2 ^ 64 := by rw [hpG]; simp [Nock.Atoms.p, Nock.Field.p]

theorem hHA : HdlOK (ringChar (ZMod p)) (DA).H := ComplJ8Data.hdlOK p Rg Rt hgen

theorem hHA' : HdlOK p (DA).H := by have := hHA Rt hgen (p := p); rwa [ZMod.ringChar_zmod_n] at this

/-- **`hpair` at the run** (from `hop5` alone). -/
theorem hpairA (hpG : p = Nock.Atoms.p) (hop5 : ComplJ8.ProgOp5OK p t) :
    ∀ u, InTree t u → isPair (DA).H (rowOfSkelX u.label) →
      HonestCompX.PairOK (F := ZMod p) ((DA).pd (rowOfSkelX u.label)) :=
  hpair9 hgen (hHA (p := p) Rt hgen) (p63_of hpG) _ hop5

/-! ### The publics -/

theorem hpubA (χ : Coins frameJ8 K) :
    pubCA δ b Rt hgen χ 0 = hk (DA).H s ∧ pubCA δ b Rt hgen χ 1 = hv (DA).H s ∧
    pubCA δ b Rt hgen χ 2 = hk (DA).H f ∧ pubCA δ b Rt hgen χ 3 = hv (DA).H f ∧
    pubCA δ b Rt hgen χ 4 = hk (DA).H r ∧ pubCA δ b Rt hgen χ 5 = hv (DA).H r := by
  have h := ComplJ9BComp.labelJ9_eq (c := cJ s f r) (hHA' (p := p) Rt hgen)
  have hl : ∀ j < 6, pubCA δ b Rt hgen χ j = (ClaimJ9.labelJ9 p (cJ s f r) (mA Rt hgen)).getD j 0 :=
    fun j hj => ClaimJ9.pubVJ9_label δ b _ _ _ _ χ j hj
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rw [hl _ (by norm_num), h] <;> simp [hlX, cJ]

/-- **The walk seed** at the twin root (the root's label is the J-8 root's, `nodeLab_gen`). -/
theorem hpSA (χ : Coins frameJ8 K) :
    limbVal b (pubCA δ b Rt hgen χ) pubSeed = Walk.curCol (nodeVA b Rt hgen χ) (W9 t) 1 * αA b χ := by
  have hlab := genX_label hgen
  have hroot : tripOf t = ((cJ s f r).subject, (cJ s f r).formula, (cJ s f r).result) := by
    simp [tripOf, cJ, hlab.1, hlab.2.1, hlab.2.2.1]
  have hcur : Walk.curCol (nodeVA b Rt hgen χ) (W9 t) 1 =
      Nock.NockVMROM.Thm54.VclL.Handle.rlcL (γA b χ) 0
        ((hlX (F := ZMod p) (DA).H ((cJ s f r).subject, (cJ s f r).formula, (cJ s f r).result)).map
          (algebraMap (ZMod p) K)) := by
    have h0 : (W9 t)[0]? = some (genX9T t) := by
      rw [W9, bfsForest_cons_eq _ (List.cons_ne_nil _ _)]; simp
    simp only [Walk.curCol, h0, Nat.sub_self, Option.map_some, Option.getD_some, nodeVA,
      ComplJ9AReadsAt.nodeV9, ComplJ9AReadsAt.nodeLab_gen, hroot]
  rw [hcur, show αA b χ = χ ⟨13, by decide⟩ from InhabJ8Comp.αC0_eq b χ,
    show γA b χ = χ ⟨14, by decide⟩ from InhabJ8Comp.γC0_eq b χ]
  rw [show limbVal b (pubCA δ b Rt hgen χ) pubSeed =
      ClaimJ9.seedJ9 (p := p) (cJ s f r) (mA Rt hgen) (toVS (toVSQ χ)) from
    ClaimJ9.limb_pubVJ9_seed δ b _ _ _ _ χ]
  unfold ClaimJ9.seedJ9
  rw [ComplJ9BComp.labelJ9_eq (hHA' (p := p) Rt hgen)]
  simp [hlX, Nock.NockVMROM.Thm54.VclL.Handle.rlcL, toVS, toVSQ, cAlphaW, cGamW, List.zipIdx]
  ring

/-- **The six accumulator terminals** (twin of `ComplJ8Comp.hρ` / `ComplJ9BComp.hρ9`): the record's `ρ`, `ρS` are
the `accV9` totals, which read no public (`accV9_pub`). -/
theorem hρA (χ : Coins frameJ8 K) :
    ∀ a < 6, ∀ k : Fin 3, pubCA δ b Rt hgen χ (pubOfA a + k) =
      coord b (accV9 b δ (DA).H (DA).pd (idOfA (p := p) Rt hgen) (W9 t) (chalVJ8 b χ) (pubCA δ b Rt hgen χ) a (N9 t)) k := by
  intro a ha k
  have h12 : 12 ≤ pubOfA a + k := by
    interval_cases a <;> simp [pubOfA, pubRhoX, pubRhoXIm, pubRhoP, pubRhoPIm, pubRhoSX, pubRhoSXi] <;> omega
  rw [accV9_pub b δ _ _ _ _ _ _ (fun _ => 0)]
  change _ = coord b (accTA δ b Rt hgen χ a) k
  unfold pubCA
  rw [ClaimJ9.pubVJ9_hi δ b _ _ _ _ χ _ h12]
  interval_cases a <;> fin_cases k <;>
    simp [pubOfA, pubVJ8, pubVHQ, pubVH, ρA, ρSA, pubRhoX, pubRhoXIm, pubRhoP, pubRhoPIm,
      pubRhoSX, pubRhoSXi, Quad.re_mk, Quad.im_mk]

/-! ### Good coins -/

variable (hpG : p = Nock.Atoms.p) (h31A : ComplJ9ARun.Rows31A (j9aDataOf p Rg Rt hgen))

include hgen in
/-- An `s10B` row of the twin is an op-10 row. -/
theorem s10B_rows : ∀ j < N9 t, (rowAt9 (W9 t) (j + 1)).chip = .s10B → (rowAt9 (W9 t) (j + 1)).rn.st = .s10 := by
  intro j hj hc
  have hjW : j < (W9 t).length := by rw [N9_def] at hj; exact hj
  have hrow : rowAt9 (W9 t) (j + 1) = ((W9 t)[j]'hjW).label := by
    simp [rowAt9, List.getElem?_eq_getElem hjW]
  have hmem : (W9 t)[j]'hjW ∈ bfsForest [genX9T t] := List.getElem_mem hjW
  obtain ⟨c, hc', hcu⟩ := (mem_bfsForest _ _).1 hmem
  simp only [List.mem_singleton] at hc'
  subst hc'
  have hsem := ComplJ9AGen.semN9_of_node9 (ComplJ9AGen.genX9T_inTree hgen hcu)
  rw [hrow] at hc ⊢
  simp only [ComplJ9AGen.SemN9, hc] at hsem
  exact hsem.2.1

include hpG h31A in
/-- **`hnb` at a good coin**: the twin slot poles `compPoles9` are in the record's bad list. -/
theorem hnbA {χ : Coins frameJ8 K} (hχ : (BRun9A δ b Rt hgen hpG h31A).Good χ) :
    ∀ j < N9 t, ∀ S ∈ slotsX9 (F := ZMod p),
      dVal b δ S (env0 (DA).H (DA).pd (idOfA (p := p) Rt hgen) (W9 t) (chalVJ8 b χ) (pubCA δ b Rt hgen χ) j) ≠ 0 ∨
        aVal b δ S (env0 (DA).H (DA).pd (idOfA (p := p) Rt hgen) (W9 t) (chalVJ8 b χ) (pubCA δ b Rt hgen χ) j) = 0 :=
  compDen9_ok (p := p) (K := K) δ b _ _ _ _ _ _ χ (s10B_rows hgen) fun e he =>
    good_fam δ b Rt hgen hpG h31A hχ _ (List.mem_append_right _ (by unfold famsNew; simp)) e he

include hpG h31A in
/-- **`hord` at a good coin.** -/
theorem hordA {χ : Coins frameJ8 K} (hχ : (BRun9A δ b Rt hgen hpG h31A).Good χ) :
    (bfsForest [genX9T t]).length ≤ orderOf (αA b χ) := by
  show (W9 t).length ≤ orderOf (InhabJ8Comp.αC0 b χ)
  rw [InhabJ8Comp.αC0_eq, ← N9_def]
  exact good_ord9 δ b Rt hgen hpG h31A hχ

/-! ### The nodes -/

include hpG h31A in
theorem n9_le : N9 t ≤ 2 ^ htA (DA) :=
  le_two_pow_htA (DA) (List.mem_append_right _ List.mem_cons_self)

include hpG h31A in
/-- **`hinjX`.** -/
theorem hinjXA : Function.Injective (BRun9A δ b Rt hgen hpG h31A).Pb.nodes :=
  (powN_ok (oA Rt hgen hpG h31A) (n9_le Rt hgen hpG h31A)).1

include hpG h31A in
/-- **`hadjX`.** -/
theorem hadjXA : ∀ (i : Fin (BRun9A δ b Rt hgen hpG h31A).Pb.n) (hi : (i : ℕ) + 1 < (BRun9A δ b Rt hgen hpG h31A).Pb.n),
    (BRun9A δ b Rt hgen hpG h31A).Pb.nodes ⟨(i : ℕ) + 1, hi⟩ =
      (BRun9A δ b Rt hgen hpG h31A).Pb.nodes i * (BRun9A δ b Rt hgen hpG h31A).Pb.orbit.ω :=
  (powN_ok (oA Rt hgen hpG h31A) (n9_le Rt hgen hpG h31A)).2

include hpG h31A in
/-- **`hsatX` at every good coin of `BRun9A`.**  Binders: `hax9` (J-9 A axis) and `hop5` (op-5 depth). -/
theorem hsatXA (hax9 : ComplJ9ABinders.ProgAxOK9A p t) (hop5 : ComplJ8.ProgOp5OK p t)
    (χ : Coins frameJ8 K) (hχ : (BRun9A δ b Rt hgen hpG h31A).Good χ) :
    RAP.SatisfiesWithPreprocessing
      (computeChipVCLHX9 (BRun9A δ b Rt hgen hpG h31A).Pb.hn (BRun9A δ b Rt hgen hpG h31A).Pb.nodes b δ (chalVJ8 b χ)
        (ClaimJ9.pubVJ9 δ b (cJ s f r) ((BRun9A δ b Rt hgen hpG h31A).M χ).m ((BRun9A δ b Rt hgen hpG h31A).M χ).ρ
          ((BRun9A δ b Rt hgen hpG h31A).M χ).ρS χ) (BRun9A δ b Rt hgen hpG h31A).Pb.orbit)
      (qX9 δ b (BRun9A δ b Rt hgen hpG h31A).Pb ((BRun9A δ b Rt hgen hpG h31A).tr χ) (chalVJ8 b χ)
        (ClaimJ9.pubVJ9 δ b (cJ s f r) ((BRun9A δ b Rt hgen hpG h31A).M χ).m ((BRun9A δ b Rt hgen hpG h31A).M χ).ρ
          ((BRun9A δ b Rt hgen hpG h31A).M χ).ρS χ)) := by
  show RAP.SatisfiesWithPreprocessing
    (computeChipVCLHX9 (PbA Rt hgen hpG h31A).hn (powN (oA Rt hgen hpG h31A) (N9 t)) b δ (chalVJ8 b χ)
      (pubCA δ b Rt hgen χ) (oA Rt hgen hpG h31A))
    (trCA δ b Rt hgen χ (powN (oA Rt hgen hpG h31A) (N9 t)))
  rw [trCA_def]
  have hN : N9 t = (bfsForest [genX9T t]).length := N9_def t
  have hok := powN_ok (oA Rt hgen hpG h31A) (n9_le Rt hgen hpG h31A)
  have hρ := hρA δ b Rt hgen χ
  exact HonestSatX9.computeChipVCLHX9_honest_sat δ (DA).H (DA).pd (idOfA (p := p) Rt hgen) (genX9T t) (nodeVA b Rt hgen χ)
    (αA b χ) (γA b χ) (hordA δ b Rt hgen hpG h31A hχ) (PbA Rt hgen hpG h31A).hn hN
    (powN (oA Rt hgen hpG h31A) (N9 t)) hok.1 b (chalVJ8 b χ) (pubCA δ b Rt hgen χ) (oA Rt hgen hpG h31A)
    (fun i hi => (hok.2 i hi).trans (mul_comm _ _)) rfl rfl
    (ClaimJ9.pubVJ9_IC δ b _ _ _ _ χ) (hpSA δ b Rt hgen χ) (ClaimJ9.pubVJ9_out δ b _ _ _ _ χ)
    (ComplJ9ABase.hbase9 hpG hgen hax9 hop5 (DA).H (DA).pd (DA).acs.length (hHA (p := p) Rt hgen)
      (hpairA Rt hgen hpG hop5) hN (pubCA δ b Rt hgen χ) (hpubA δ b Rt hgen χ))
    (ComplJ9AReadsAt.readsAt9_honest_zmod (DA).H (DA).pd (DA).acs.length (hHA' (p := p) Rt hgen) (p62_of hpG) (p64_of hpG)
      hgen (αA b χ) (γA b χ))
    hρ (hnbA δ b Rt hgen hpG h31A hχ)

end Run

end

end Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AOfComp

section Axioms
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AOfComp
#print axioms accV9_pub
#print axioms hex9
#print axioms compDen9_ok
#print axioms hpair9
#print axioms hpSA
#print axioms hρA
#print axioms hnbA
#print axioms hinjXA
#print axioms hadjXA
#print axioms hsatXA
end Axioms
