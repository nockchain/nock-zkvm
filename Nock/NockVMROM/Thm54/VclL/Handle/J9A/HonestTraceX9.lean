/-
  Nock/NockVMROM/Thm54/VclL/Handle/J9A/HonestTraceX9.lean

* §2 the trace, in TWIN column order, in three stages: `baseT9` (`colX9` of BFS row `j + 1` on the round-0
    columns), `preT9` (+ the slot inverse limbs `69..92`, `A · D⁻¹` at `env0`), `trX9` (+ the accumulator
    prefix sums `93..110` at `env1`, the walk limbs `111..122`).
  * §3 the limb readings; §4 the congruences (reads through the round-0 set).
  * §5 `polyX9` — Lagrange interpolation of the trace in RAP column order (`invPermX9`), `polyX9_via_trace` /
    `polyX9_via_next` (the permuted row environment reads the twin trace below `137`), the preprocessing
    columns, and **`computeChipVCLHX9_sat_of`**, the converse of `ChipHX9RAP.computeChipVCLHX9_sat_twin`.
  * §6 **`computeChipVCLHX9_honest_sat`**: generic in the J-9 A tree `t9` (`W = bfsForest [t9]`), with the
    arithmetic / equality base gates (`hbase`) and the walk label reads (`hrd : ReadsAt9`) as hypotheses per row.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.HonestWalkX9

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.HonestTraceX9

open Nock Nock.Noun Nock.Walk Nock.Jet Nock.Edit Nock.Edit.GenX Nock.Reified Nock.Framework Module Polynomial
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler
open Nock.NockVMROM.Thm54.T0Tower Nock.NockVMROM.Thm54.T0TowerFP
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.MonolithicRAP Nock.Framework.Reify
open Nock.NockVMROM.Thm54.VclL.Compute.LogUp Nock.NockVMROM.Thm54.VclL.Compute.TowerD
open Nock.NockVMROM.Thm54.VclL.Handle.ChipH (Hd cc notC selS mapC mapM chalAlphaW chalGammaW pubIC pubSeed
  pubOut pubRhoX pubRhoP)
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHQ (pubRhoXIm pubRhoPIm)
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHX
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHX9
open Nock.NockVMROM.Thm54.VclL.Handle.HonestSlotX
open Nock.NockVMROM.Thm54.VclL.Handle.HonestWalkX (walkEnvKX)
open Nock.NockVMROM.Thm54.VclL.Handle (evalMQ)
open Nock.NockVMROM.Thm54.VclL.HonestTraceX (okC okM envAt eval_okC eval_okM okC_mapC okM_mapM
  eval_mapC_castX okKs okKw okKc isNLX isNLX_eq cNA cNA_coord limbVal_of_cNA walkV accSpec pubOfA
  accGatesX_map)
open Nock.NockVMROM.Thm54.VclL.HonestWalkX9
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AGen (LX9)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ACompRow (colX9 hEnvX9 invPermX9 permX9_inv)

noncomputable section

/-! ## 1. The twin's read sets -/

/-- The round-0 twin columns: `0..68` and `123..136`. -/
def r0 (i : ℕ) : Bool := decide (i < 69) || (decide (123 ≤ i) && decide (i < 137))

theorem r0_iff (i : ℕ) : r0 i = true ↔ i < 69 ∨ (123 ≤ i ∧ i < 137) := by simp [r0]

/-- Slot `D / A` and accumulator activities, base side: round-0 columns of the current row. -/
def okFs9 : VarKind → ℕ → Bool
  | .traceCur, i => r0 i
  | _, _ => false

/-- Arithmetic / equality gates: round-0 columns of the current row and the publics. -/
def okB9 : VarKind → ℕ → Bool
  | .traceCur, i => r0 i
  | .publicVal, _ => true
  | _, _ => false

/-- Walk gates, base side: round-0 columns of the current / next row. -/
def okFw9 : VarKind → ℕ → Bool
  | .traceCur, i => r0 i
  | .traceNext, i => r0 i
  | _, _ => false

/-- Walk gates, base side, current row only. -/
def okFc9 : VarKind → ℕ → Bool
  | .traceCur, i => r0 i
  | _, _ => false

theorem arith_ok9 : (arithGatesX9.all (okC okB9)) = true := by decide +kernel

theorem eq_ok9 : ((eqGatesX9 (F := ℚ)).all fun g => okC okB9 g.gate) = true := by decide +kernel

theorem walk_ok9 : ((walkGatesX9 (F := ℚ)).all (okM okKw okFw9)) = true := by decide +kernel

theorem walk_shape9 : ((walkGatesX9 (F := ℚ)).all fun g => okM okKc okFc9 g || isNLX g) = true := by
  decide +kernel

theorem slotsAct_ok9 : (slotsX9 (F := ℚ)).all (fun S =>
    okC okFs9 (S.actB .x) && okC okFs9 (S.actB .p) && okC okFs9 (S.actB .s) &&
    decide (S.inv + 3 ≤ 93) && decide (S.invIm + 3 ≤ 93)) = true := by decide +kernel

theorem slotsDA_ok9 {F : Type} [Field F] (δ : F) : (slotsX9 (F := F)).all (fun S =>
    okM okKs okFs9 (slotDQ F δ S).1 && okM okKs okFs9 (slotDQ F δ S).2 &&
    okM okKs okFs9 (slotAQ F δ S).1 && okM okKs okFs9 (slotAQ F δ S).2) = true := by
  rfl

/-! ## 2. The trace (twin column order) -/

section Trace
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [Fintype K] [DecidableEq F]
  (b : Basis (Fin 3) F K) (δ : F) [Fact (¬ IsSquare (algebraMap F K δ))]

local notation "𝕂′" => Quad (algebraMap F K δ)

variable (H : Noun → ℕ × ℕ) (pd : RowNX → ℕ × (ℕ × ℕ) × (ℕ × ℕ)) (idOf : ℕ → ℕ) (W : List (NTree LX9))
  (chalV pubVal : ℕ → F)

/-- **Stage 1**: the honest columns of chip row `j` (`colX9` of BFS row `j + 1`, first / last flags). -/
def baseT9 (j c : ℕ) : F := colX9 H pd idOf (rowAt9 W (j + 1)) (fl1 (j + 1)) (llW W (j + 1)) c

/-- The stage-1 environment of chip row `j`. -/
def env0 (j : ℕ) : Env F := ⟨baseT9 H pd idOf W j, baseT9 H pd idOf W (j + 1), chalV, pubVal⟩

/-- **The honest `𝕂′` slot inverse** `A · D⁻¹` of chip row `j`, read at `env0`. -/
def invV9 (j : ℕ) (S : SlotX F) : 𝕂′ :=
  aVal b δ S (env0 H pd idOf W chalV pubVal j) * (dVal b δ S (env0 H pd idOf W chalV pubVal j))⁻¹

/-- The twin slot by index. -/
def slotAt9 : ℕ → SlotX F
  | 0 => slot0X9
  | 1 => slot1X9
  | 2 => slot2X9
  | _ => slot3X9

/-- The inverse limbs `69..92`: slot `(c − 69) / 6`, Re on offsets `0..2`, Im on `3..5`. -/
def invCol9 (j c : ℕ) : F :=
  if (c - 69) % 6 < 3 then
    cNA b (Quad.re _ (invV9 b δ H pd idOf W chalV pubVal j (slotAt9 ((c - 69) / 6)))) ((c - 69) % 6)
  else cNA b (Quad.im _ (invV9 b δ H pd idOf W chalV pubVal j (slotAt9 ((c - 69) / 6)))) ((c - 69) % 6 - 3)

/-- **Stage 2**: the round-0 columns and the slot inverses (`0` on `93..122` and from `137`). -/
def preT9 (j c : ℕ) : F :=
  if c < 69 then baseT9 H pd idOf W j c
  else if c < 93 then invCol9 b δ H pd idOf W chalV pubVal j c
  else if 123 ≤ c ∧ c < 137 then baseT9 H pd idOf W j c else 0

/-- The stage-2 environment of chip row `j`. -/
def env1 (j : ℕ) : Env F :=
  ⟨preT9 b δ H pd idOf W chalV pubVal j, preT9 b δ H pd idOf W chalV pubVal (j + 1), chalV, pubVal⟩

/-- The `ℚ`-template slots of accumulator `(bl, im)` (as in `accOf9`). -/
def slotsQ9 (bl : Bal) (im : Bool) : List (Slot ℚ) :=
  (slotsX9 (F := ℚ)).map fun S => ⟨S.actB bl, if im then S.invIm else S.inv⟩

/-- The cast slots. -/
def slotsF9 (bl : Bal) (im : Bool) : List (Slot F) :=
  (slotsQ9 bl im).map Nock.NockVMROM.Thm54.VclL.Handle.castSlot

/-- **The exclusive prefix sum** of accumulator `a`'s per-row terms at the stage-2 environments. -/
def accV9 (a i : ℕ) : K :=
  ∑ j ∈ Finset.range i,
    termVal b (slotsF9 (accSpec a).1 (accSpec a).2) (env1 b δ H pd idOf W chalV pubVal j)

variable (ln cnt acc : ℕ → K)

/-- **The honest full trace of `computeChipVCLHX9`** in TWIN column order (row `j`, column `c`; `0` from `137`). -/
def trX9 (j c : ℕ) : F :=
  if c < 93 then preT9 b δ H pd idOf W chalV pubVal j c
  else if c < 111 then cNA b (accV9 b δ H pd idOf W chalV pubVal ((c - 93) / 3) j) ((c - 93) % 3)
  else if c < 123 then cNA b (walkV ln cnt acc ((c - 111) / 3) (j + 1)) ((c - 111) % 3)
  else preT9 b δ H pd idOf W chalV pubVal j c

/-! ## 3. Limb readings -/

theorem trX9_base (j c : ℕ) (hc : r0 c = true) :
    trX9 b δ H pd idOf W chalV pubVal ln cnt acc j c = baseT9 H pd idOf W j c := by
  rw [r0_iff] at hc
  unfold trX9 preT9
  split_ifs <;> first | rfl | omega

theorem trX9_pre (j c : ℕ) (hc : c < 93 ∨ 123 ≤ c) :
    trX9 b δ H pd idOf W chalV pubVal ln cnt acc j c = preT9 b δ H pd idOf W chalV pubVal j c := by
  unfold trX9
  split_ifs <;> first | rfl | omega

theorem trX9_inv (j s o : ℕ) (hs : s < 4) (ho : o < 6) :
    trX9 b δ H pd idOf W chalV pubVal ln cnt acc j (69 + 6 * s + o) =
      if o < 3 then cNA b (Quad.re _ (invV9 b δ H pd idOf W chalV pubVal j (slotAt9 s))) o
      else cNA b (Quad.im _ (invV9 b δ H pd idOf W chalV pubVal j (slotAt9 s))) (o - 3) := by
  have h1 : (69 + 6 * s + o - 69) / 6 = s := by omega
  have h2 : (69 + 6 * s + o - 69) % 6 = o := by omega
  rw [trX9_pre _ _ _ _ _ _ _ _ _ _ _ _ _ (Or.inl (by omega))]
  unfold preT9 invCol9
  rw [if_neg (by omega), if_pos (by omega), h1, h2]

theorem limb_inv9 (j s : ℕ) (hs : s < 4) :
    limbVal b (trX9 b δ H pd idOf W chalV pubVal ln cnt acc j) (69 + 6 * s) =
      Quad.re _ (invV9 b δ H pd idOf W chalV pubVal j (slotAt9 s)) := by
  refine limbVal_of_cNA b _ _ _ fun k => ?_
  rw [trX9_inv b δ H pd idOf W chalV pubVal ln cnt acc j s k hs (by omega), if_pos k.isLt]

theorem limb_invIm9 (j s : ℕ) (hs : s < 4) :
    limbVal b (trX9 b δ H pd idOf W chalV pubVal ln cnt acc j) (72 + 6 * s) =
      Quad.im _ (invV9 b δ H pd idOf W chalV pubVal j (slotAt9 s)) := by
  refine limbVal_of_cNA b _ _ _ fun k => ?_
  have e : 72 + 6 * s + (k : ℕ) = 69 + 6 * s + ((k : ℕ) + 3) := by omega
  rw [e, trX9_inv b δ H pd idOf W chalV pubVal ln cnt acc j s _ hs (by omega), if_neg (by omega)]
  simp

theorem trX9_acc (j a : ℕ) (ha : a < 6) (k : Fin 3) :
    trX9 b δ H pd idOf W chalV pubVal ln cnt acc j (93 + 3 * a + k) =
      coord b (accV9 b δ H pd idOf W chalV pubVal a j) k := by
  have h1 : (93 + 3 * a + (k : ℕ) - 93) / 3 = a := by omega
  have h2 : (93 + 3 * a + (k : ℕ) - 93) % 3 = k := by omega
  unfold trX9
  rw [if_neg (by omega), if_pos (by omega), h1, h2, cNA_coord]

theorem limb_walk9 (j w : ℕ) (hw : w < 4) :
    limbVal b (trX9 b δ H pd idOf W chalV pubVal ln cnt acc j) (111 + 3 * w) = walkV ln cnt acc w (j + 1) := by
  refine limbVal_of_cNA b _ _ _ fun k => ?_
  have h1 : (111 + 3 * w + (k : ℕ) - 111) / 3 = w := by omega
  have h2 : (111 + 3 * w + (k : ℕ) - 111) % 3 = k := by omega
  unfold trX9
  rw [if_neg (by omega), if_neg (by omega), if_pos (by omega), h1, h2]

omit [FiniteDimensional F K] [Fintype K] [DecidableEq F] in
/-- Two traces that agree on a limb's three columns read the same `𝕂` value there. -/
theorem limbVal_congr (f g : ℕ → F) (c0 : ℕ) (h : ∀ k : Fin 3, f (c0 + k) = g (c0 + k)) :
    limbVal b f c0 = limbVal b g c0 := by
  unfold limbVal
  exact Finset.sum_congr rfl fun k _ => by rw [h k]

theorem baseT9_17 (j : ℕ) : baseT9 H pd idOf W j 17 = (if j = 0 then 1 else 0 : F) := by
  simp [baseT9, colX9_17, fl1]

theorem baseT9_18 (j : ℕ) : baseT9 H pd idOf W j 18 = (if j + 1 = W.length then 1 else 0 : F) := by
  simp [baseT9, colX9_18, llW]

end Trace

/-! ## 4. Congruences -/

section Cong
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [Fintype K] [DecidableEq F]
  (b : Basis (Fin 3) F K) (δ : F) [Fact (¬ IsSquare (algebraMap F K δ))]

theorem slot_ok9 {S : SlotX F} (hS : S ∈ slotsX9 (F := F)) :
    okM okKs okFs9 (slotDQ F δ S).1 = true ∧ okM okKs okFs9 (slotDQ F δ S).2 = true ∧
    okM okKs okFs9 (slotAQ F δ S).1 = true ∧ okM okKs okFs9 (slotAQ F δ S).2 = true := by
  have h := List.all_eq_true.mp (slotsDA_ok9 δ) S hS
  simp only [Bool.and_eq_true] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

/-- **The twin slot `D / A` read only round-0 columns and the coins** (`slotsDA_ok9`). -/
theorem dVal_aVal_congr9 {S : SlotX F} (hS : S ∈ slotsX9 (F := F)) (e1 e2 : Env F)
    (htr : ∀ c, r0 c = true → e1.trace c = e2.trace c) (hch : e1.chal = e2.chal) :
    dVal b δ S e1 = dVal b δ S e2 ∧ aVal b δ S e1 = aVal b δ S e2 := by
  obtain ⟨h1, h2, h3, h4⟩ := slot_ok9 δ hS
  have hK : ∀ k i, okKs k i = true →
      envAt (Compute.TowerD.gatherEnv b e1) k i = envAt (Compute.TowerD.gatherEnv b e2) k i := by
    intro k i hk
    cases k <;> simp [okKs] at hk
    simp [envAt, Compute.TowerD.gatherEnv, hch]
  have hF : ∀ k i, okFs9 k i = true → envAt e1 k i = envAt e2 k i := by
    intro k i hk
    cases k <;> simp only [okFs9, Bool.false_eq_true] at hk
    exact htr i hk
  simp only [dVal, aVal, Q.val]
  rw [eval_okM okKs okFs9 _ h1 _ _ _ _ hK hF, eval_okM okKs okFs9 _ h2 _ _ _ _ hK hF,
    eval_okM okKs okFs9 _ h3 _ _ _ _ hK hF, eval_okM okKs okFs9 _ h4 _ _ _ _ hK hF]
  exact ⟨rfl, rfl⟩

theorem slotsF9_mem {bl : Bal} {im : Bool} {s : Slot F} (hs : s ∈ slotsF9 (F := F) bl im) :
    ∃ S ∈ slotsX9 (F := ℚ),
      s = Nock.NockVMROM.Thm54.VclL.Handle.castSlot ⟨S.actB bl, if im then S.invIm else S.inv⟩ := by
  simp only [slotsF9, slotsQ9, List.map_map, List.mem_map, Function.comp] at hs
  obtain ⟨S, hS, rfl⟩ := hs
  exact ⟨S, hS, rfl⟩

/-- **An accumulator term reads only the columns `< 93` and `123..136`** (`slotsAct_ok9`). -/
theorem termVal_congr9 (bl : Bal) (im : Bool) (e1 e2 : Env F)
    (htr : ∀ c, (c < 93 ∨ (123 ≤ c ∧ c < 137)) → e1.trace c = e2.trace c) :
    termVal b (slotsF9 bl im) e1 = termVal b (slotsF9 bl im) e2 := by
  unfold termVal
  congr 1
  refine List.map_congr_left fun s hs => ?_
  obtain ⟨S, hS, rfl⟩ := slotsF9_mem hs
  have hf := List.all_eq_true.mp slotsAct_ok9 S hS
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hf
  obtain ⟨⟨⟨⟨hx, hp⟩, hs'⟩, hi⟩, hii⟩ := hf
  have hact : okC okFs9 (S.actB bl) = true := by cases bl <;> assumption
  have hF : ∀ k i, okFs9 k i = true → envAt e1 k i = envAt e2 k i := by
    intro k i hk
    cases k <;> simp only [okFs9, Bool.false_eq_true] at hk
    rw [r0_iff] at hk
    exact htr i (by omega)
  have hbase : (if im then S.invIm else S.inv) + 3 ≤ 93 := by split <;> assumption
  have hb2 : (Nock.NockVMROM.Thm54.VclL.Handle.castSlot (F := F)
      ⟨S.actB bl, if im then S.invIm else S.inv⟩).invBase = (if im then S.invIm else S.inv) := rfl
  have hev : (Nock.NockVMROM.Thm54.VclL.Handle.castSlot (F := F)
      ⟨S.actB bl, if im then S.invIm else S.inv⟩).act.eval e1 =
      (Nock.NockVMROM.Thm54.VclL.Handle.castSlot (F := F)
      ⟨S.actB bl, if im then S.invIm else S.inv⟩).act.eval e2 :=
    eval_okC okFs9 _ (by
      show okC okFs9 (mapC (fun q : ℚ => (q : F)) (S.actB bl)) = true
      rw [okC_mapC]; exact hact) e1 e2 hF
  rw [hev, hb2]
  congr 1
  unfold limbVal
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [htr _ (by have := k.isLt; omega)]

/-- **The arithmetic / equality gates read only round-0 columns and the publics** (`arith_ok9`, `eq_ok9`). -/
theorem evalQX_congr9 (g : CoeffExpr ℚ) (h : okC okB9 g = true) (e1 e2 : Env F)
    (htr : ∀ c, r0 c = true → e1.trace c = e2.trace c) (hpub : e1.pub = e2.pub) :
    evalQX g e1 = evalQX g e2 := by
  rw [← eval_mapC_castX, ← eval_mapC_castX]
  refine eval_okC okB9 _ (by rw [okC_mapC]; exact h) e1 e2 fun k i hk => ?_
  cases k <;> simp only [okB9, Bool.false_eq_true] at hk
  · exact htr i hk
  · simp [envAt, hpub]

theorem accGatesHX9_mem {g : CoeffExpr ℚ} (hg : g ∈ (accGatesHX9 : List (CoeffExpr ℚ))) :
    ∃ a < 6, g ∈ accGatesX (slotsQ9 (accSpec a).1 (accSpec a).2) (93 + 3 * a) (pubOfA a) := by
  simp only [accGatesHX9, List.mem_append] at hg
  rcases hg with ((((h | h) | h) | h) | h) | h
  · exact ⟨0, by norm_num, h⟩
  · exact ⟨1, by norm_num, h⟩
  · exact ⟨2, by norm_num, h⟩
  · exact ⟨3, by norm_num, h⟩
  · exact ⟨4, by norm_num, h⟩
  · exact ⟨5, by norm_num, h⟩

theorem slot_index9 {S : SlotX F} (hS : S ∈ slotsX9 (F := F)) :
    ∃ s < 4, S = slotAt9 s ∧ S.inv = 69 + 6 * s ∧ S.invIm = 72 + 6 * s := by
  simp only [slotsX9, List.mem_cons, List.not_mem_nil, or_false] at hS
  rcases hS with rfl | rfl | rfl | rfl
  · exact ⟨0, by norm_num, rfl, rfl, rfl⟩
  · exact ⟨1, by norm_num, rfl, rfl, rfl⟩
  · exact ⟨2, by norm_num, rfl, rfl, rfl⟩
  · exact ⟨3, by norm_num, rfl, rfl, rfl⟩

end Cong

/-! ## 5. The trace polynomials (RAP order) and the converse transport -/

section Poly
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [Fintype K] [DecidableEq F]
  (b : Basis (Fin 3) F K) (δ : F) [Fact (¬ IsSquare (algebraMap F K δ))]
  (H : Noun → ℕ × ℕ) (pd : RowNX → ℕ × (ℕ × ℕ) × (ℕ × ℕ)) (idOf : ℕ → ℕ) (W : List (NTree LX9))
  (chalV pubVal : ℕ → F) (ln cnt acc : ℕ → K) {n : ℕ} (nodes : Fin n → F)

/-- **The honest trace polynomials of `computeChipVCLHX9`**: RAP column `d` interpolates twin column
`invPermX9 d`. -/
def polyX9 (w : ℕ) : Fin w → F[X] := fun d =>
  Lagrange.interpolate Finset.univ nodes (fun i : Fin n =>
    trX9 b δ H pd idOf W chalV pubVal ln cnt acc (i : ℕ) (invPermX9 (d : ℕ)))

theorem polyX9_eval (hinj : Function.Injective nodes) {w : ℕ} (d : Fin w) (i : Fin n) :
    (polyX9 b δ H pd idOf W chalV pubVal ln cnt acc nodes w d).eval (nodes i) =
      trX9 b δ H pd idOf W chalV pubVal ln cnt acc (i : ℕ) (invPermX9 (d : ℕ)) :=
  Lagrange.eval_interpolate_at_node _ hinj.injOn (Finset.mem_univ i)

theorem permX9_lt137 (c : ℕ) (hc : c < 137) : permX9 c < 137 := by
  simp only [permX9]; split_ifs <;> omega

/-- **The permuted row environment reads the twin trace** below `137`. -/
theorem polyX9_via_trace (hinj : Function.Injective nodes) {w : ℕ} (hw : 137 ≤ w) (ω : F) (i : Fin n)
    (c : ℕ) (hc : c < 137) :
    (Env.viaPerm permX9 (Reify.envOfTrace (polyX9 b δ H pd idOf W chalV pubVal ln cnt acc nodes w) ω
      (nodes i) chalV pubVal)).trace c = trX9 b δ H pd idOf W chalV pubVal ln cnt acc (i : ℕ) c := by
  have hl : permX9 c < w := by have := permX9_lt137 c hc; omega
  simp only [Env.viaPerm, Reify.envOfTrace]
  rw [dif_pos hl]
  exact (polyX9_eval b δ H pd idOf W chalV pubVal ln cnt acc nodes hinj ⟨permX9 c, hl⟩ i).trans
    (congrArg _ (permX9_inv c hc))

theorem polyX9_via_next (hinj : Function.Injective nodes) {w : ℕ} (hw : 137 ≤ w) (ω : F) (i : Fin n)
    (hi : (i : ℕ) + 1 < n) (hadj : nodes ⟨(i : ℕ) + 1, hi⟩ = ω * nodes i) (c : ℕ) (hc : c < 137) :
    (Env.viaPerm permX9 (Reify.envOfTrace (polyX9 b δ H pd idOf W chalV pubVal ln cnt acc nodes w) ω
      (nodes i) chalV pubVal)).traceNext c =
        trX9 b δ H pd idOf W chalV pubVal ln cnt acc ((i : ℕ) + 1) c := by
  have hl : permX9 c < w := by have := permX9_lt137 c hc; omega
  simp only [Env.viaPerm, Reify.envOfTrace]
  rw [dif_pos hl, ← hadj]
  exact (polyX9_eval b δ H pd idOf W chalV pubVal ln cnt acc nodes hinj ⟨permX9 c, hl⟩
    ⟨(i : ℕ) + 1, hi⟩).trans (congrArg _ (permX9_inv c hc))

theorem polyX9_first (w : ℕ) (hw : 17 < w) :
    polyX9 b δ H pd idOf W chalV pubVal ln cnt acc nodes w ⟨17, hw⟩ = firstRowMask nodes := by
  unfold polyX9 firstRowMask
  congr 1
  funext i
  show trX9 b δ H pd idOf W chalV pubVal ln cnt acc (i : ℕ) 17 = _
  rw [trX9_base b δ H pd idOf W chalV pubVal ln cnt acc _ 17 (by decide), baseT9_17]

theorem polyX9_last (hn : 0 < n) (hN : W.length = n) (w : ℕ) (hw : 18 < w) :
    polyX9 b δ H pd idOf W chalV pubVal ln cnt acc nodes w ⟨18, hw⟩ = lastRowMask hn nodes := by
  unfold polyX9 lastRowMask
  congr 1
  funext i
  show trX9 b δ H pd idOf W chalV pubVal ln cnt acc (i : ℕ) 18 = _
  rw [trX9_base b δ H pd idOf W chalV pubVal ln cnt acc _ 18 (by decide), baseT9_18, hN]
  have : (i = ⟨n - 1, Nat.sub_lt hn (by omega)⟩) ↔ (i : ℕ) + 1 = n := by
    constructor
    · intro h; subst h; simp; omega
    · intro h; apply Fin.ext; simp; omega
  simp only [this]

end Poly

section Transport
variable {F K : Type} [Field F] [Field K] [Algebra F K]

/-- **The converse of `computeChipVCLHX9_sat_twin`**: the preprocessing binding plus every twin gate at the
permuted row environment of every row node is satisfaction with preprocessing. -/
theorem computeChipVCLHX9_sat_of [FiniteDimensional F K] {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F)
    (b : Basis (Fin 3) F K) (δ : F) (chalV pubVal : ℕ → F) (orbit : StrictOrbitDomain F 3 h)
    (P : Fin (computeChipVCLHX9 hn nodes b δ chalV pubVal orbit).rap.w → F[X])
    (hbind : (computeChipVCLHX9 hn nodes b δ chalV pubVal orbit).BindsPreprocessing P)
    (hall : ∀ x ∈ rowNodeSet nodes, ∀ g ∈ gatesHX9 b δ,
      g.eval (Env.viaPerm permX9 (Reify.envOfTrace P orbit.ω x chalV pubVal)) = 0) :
    RAP.SatisfiesWithPreprocessing (computeChipVCLHX9 hn nodes b δ chalV pubVal orbit) P := by
  refine ⟨?_, hbind⟩
  intro i x hx
  have h1 := Nock.Framework.Reify.compose_eval
    (computeChipVCLHX9 hn nodes b δ chalV pubVal orbit).rap P i x
  have h2 : (computeChipVCLHX9 hn nodes b δ chalV pubVal orbit).rap.C i =
      coeffToMv chalV pubVal ((gatesHX9P b δ).get i) := rfl
  rw [h1, h2]
  exact (eval_coeffToMv (w := 137) P orbit.ω x chalV pubVal ((gatesHX9P b δ).get i)).trans
    ((gatesHX9P_eval b δ _).mpr (hall x hx) _ (List.get_mem _ _))

/-- `sat_iff` for the twin, through the permutation. -/
theorem computeChipVCLHX9_sat_iff [FiniteDimensional F K] {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F)
    (b : Basis (Fin 3) F K) (δ : F) (chalV pubVal : ℕ → F) (orbit : StrictOrbitDomain F 3 h)
    (P : Fin (computeChipVCLHX9 hn nodes b δ chalV pubVal orbit).rap.w → F[X]) :
    RAP.SatisfiesWithPreprocessing (computeChipVCLHX9 hn nodes b δ chalV pubVal orbit) P ↔
      (computeChipVCLHX9 hn nodes b δ chalV pubVal orbit).BindsPreprocessing P ∧
        ∀ x ∈ rowNodeSet nodes, ∀ g ∈ gatesHX9 b δ,
          g.eval (Env.viaPerm permX9 (Reify.envOfTrace P orbit.ω x chalV pubVal)) = 0 :=
  ⟨fun hs => ⟨hs.2, fun x hx => computeChipVCLHX9_sat_twin hn nodes b δ chalV pubVal orbit P hs.1 x hx⟩,
    fun h => computeChipVCLHX9_sat_of hn nodes b δ chalV pubVal orbit P h.1 h.2⟩

end Transport

end

end Nock.NockVMROM.Thm54.VclL.HonestTraceX9

section Axioms
open Nock.NockVMROM.Thm54.VclL.HonestTraceX9
#print axioms arith_ok9
#print axioms eq_ok9
#print axioms walk_ok9
#print axioms walk_shape9
#print axioms slotsAct_ok9
#print axioms slotsDA_ok9
#print axioms limb_inv9
#print axioms limb_invIm9
#print axioms trX9_acc
#print axioms limb_walk9
#print axioms dVal_aVal_congr9
#print axioms termVal_congr9
#print axioms evalQX_congr9
#print axioms polyX9_via_trace
#print axioms polyX9_via_next
#print axioms polyX9_first
#print axioms polyX9_last
#print axioms computeChipVCLHX9_sat_of
#print axioms computeChipVCLHX9_sat_iff
end Axioms
