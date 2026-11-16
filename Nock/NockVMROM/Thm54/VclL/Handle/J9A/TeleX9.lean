/-
  Nock/NockVMROM/Thm54/VclL/Handle/J9A/TeleX9.lean

* `slotsX9_cast`, `termQX9_row` (row terminal at a one-hot over the 20 twin states, base gates
    `BaseHoldsX9`), `termQX9_eq`, `accX9_rows`;
  * `BCtx9` — accepted twin chip, injective adjacent nodes, char bound, and the one-hot FIELD `oh`;
  * `slotX9_of_sat`, `masksB9`, `shiftB9`, `compute_balanceX9`, `compute_balanceX9_keys`, `compReqsX9_sum`;
  * `consQX9_activeX9`, `reqsJ9`, `servedP_of_balancesJ9`.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.ChipHX9RAP
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.CompReqsX9
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.RowSemSatX9
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.RowSemChipX9
import Nock.NockVMROM.Thm54.VclL.Handle.ServedJ8
import Nock.NockVMROM.Thm54.VclL.Handle.DenXJ8
import Nock.NockVMROM.Thm54.VclL.Handle.TeleCQX

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Nock.NockVMROM.Thm54.VclL.Handle.TeleX9

open Nock Nock.Reified Nock.Framework Nock.Edit Module Polynomial
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler Nock.NockVMROM.Thm54.T0Tower Nock.NockVMROM.Thm54.T0TowerFP
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.MonolithicRAP Nock.Framework.Reify
open Nock.NockVMROM.Thm54.FiniteIO
open Nock.NockVMROM.Thm54.VclL.Compute.TowerD
open Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.ChipH (Hd cc notC selS prodL mapC)
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHQ (sumQ)
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHX
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHX9
  (slotsX9 slot0X9 slot1X9 slot2X9 slot3X9 statesX9 extSlot ents0New ents1New ents2New ents3New
   BaseHoldsX9 OneHotAt9 arith_of_base9 kind_split9 arithGatesX9 baseGatesHX9 accGatesHX9 accOf9
   prGateX9 sS0B sS10B sS10S permX9 permX9_fixes_pre gatesHX9 slotPairsX9 computeChipVCLHX9
   axRecX limbRecX computeChipVCLHX9_sat_twin Env.viaPerm)
open Nock.NockVMROM.Thm54.VclL.Handle.TeleCQX
  (castEntX castSlotX DX invQX pairFX pairDaX pairDbX aMFX slotGateQX_val_spec bool_of' termValX
   evalQX_actB mk_list_sumX mk_fsumX pairRecsB balCols accX_rows)
open Nock.NockVMROM.Thm54.VclL.Handle.TeleC (rEF slot_core)
open Nock.NockVMROM.Thm54.VclL.Handle.TeleCQ (coinsCQ coinsCV)
open Nock.NockVMROM.Thm54.VclL.Handle.DenXJ8 (mOf keyX denQX_val)
open Nock.NockVMROM.Thm54.VclL.Handle.BalanceQ (liftRec liftRec_inj)
open Nock.NockVMROM.Thm54.VclL.Handle.CompReqsX9 (consQX9 compReqsX9 envsN9)
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP

noncomputable section

/-! ## 1. The slots at `ℚ` and at `F` -/

section Cast
variable {F : Type} [Field F]

theorem slotsX9_cast : (slotsX9 (F := ℚ)).map castSlotX = (slotsX9 (F := F)) := by
  simp [slotsX9, slot0X9, slot1X9, slot2X9, slot3X9, extSlot, ents0New, ents1New, ents2New, ents3New,
    ChipHX.slot0X, ChipHX.slot1X, ChipHX.slot2X, ChipHX.slot3X, castSlotX, castEntX, mapC, notC, cc, kcE, kbE]

end Cast

/-! ## 2. Row facts at a one-hot row over the twin's 20 states -/

section Row
variable {F : Type} [Field F] {env : Env F} {j : ℕ}

theorem colBool9 (hB : BaseHoldsX9 env) {i : ℕ} (hi : (boolG (cc i) : CoeffExpr ℚ) ∈ arithGatesX9) :
    env.trace i = 0 ∨ env.trace i = 1 := by
  have a := arith_of_base9 hB hi
  simp only [boolG, cc, evalQX, Rat.cast_one] at a
  exact bool_of' a

theorem kc_bool9 (hB : BaseHoldsX9 env) {h : Hd} (hh : h ∈ allHandlesX) (hne : h ≠ xF) :
    evalQX (kcE h : CoeffExpr ℚ) env = 0 ∨ evalQX (kcE h : CoeffExpr ℚ) env = 1 := by
  have : evalQX (kcE h : CoeffExpr ℚ) env = kcV env h := by
    simp [kcE, kbE, cc, evalQX, kcV]
  rw [this]
  rcases kind_split9 hB h hh hne with ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ <;> simp [h1]

theorem kb_bool9 (hB : BaseHoldsX9 env) {h : Hd} (hh : h ∈ allHandlesX) (hne : h ≠ xF) :
    env.trace (kbX h) = 0 ∨ env.trace (kbX h) = 1 := by
  rcases kind_split9 hB h hh hne with ⟨-, h1⟩ | ⟨-, h1⟩ | ⟨-, h1⟩ <;> simp only [kbV] at h1 <;> simp [h1]

theorem slotsX9_states_ok :
    ∀ S ∈ (slotsX9 : List (SlotX ℚ)), ∀ x ∈ S.ents, (∀ i ∈ x.states, i ∈ statesX9) ∧ x.states.Nodup := by
  decide +kernel

theorem slotsX9_states_disj :
    ∀ S ∈ (slotsX9 : List (SlotX ℚ)),
      (S.ents.map (·.states)).Pairwise fun a c => ∀ i ∈ a, i ∉ c := by
  decide +kernel

theorem slotsX9_pair_disj :
    ∀ S ∈ (slotsX9 : List (SlotX ℚ)), ∀ x ∈ S.ents, ∀ i ∈ x.states, i ∉ S.pairStates := by
  decide +kernel

theorem slotsX9_extras :
    ∀ S ∈ (slotsX9 : List (SlotX ℚ)), ∀ x ∈ S.ents,
      x.extra = .const 1 ∨ x.extra = notC z1X ∨ x.extra = notC fastX ∨ x.extra = kcE xSf1 := by
  decide +kernel

theorem extra_bool9 (hB : BaseHoldsX9 env) :
    ∀ S ∈ (slotsX9 : List (SlotX ℚ)), ∀ x ∈ S.ents, evalQX x.extra env = 0 ∨ evalQX x.extra env = 1 := by
  have hz := colBool9 hB (i := z1X) (by decide +kernel)
  have hf := colBool9 hB (i := fastX) (by decide +kernel)
  have hk := kc_bool9 hB (h := xSf1) (by decide) (by decide)
  have n1 : ∀ i, (env.trace i = 0 ∨ env.trace i = 1) →
      evalQX (notC i : CoeffExpr ℚ) env = 0 ∨ evalQX (notC i : CoeffExpr ℚ) env = 1 := by
    intro i hi
    simp only [notC, cc, evalQX, Rat.cast_one]
    rcases hi with h | h <;> simp [h]
  intro S hS x hx
  rcases slotsX9_extras S hS x hx with h | h | h | h
  · rw [h]; right; simp [evalQX]
  · rw [h]; exact n1 _ hz
  · rw [h]; exact n1 _ hf
  · rw [h]; exact hk

theorem selS_onehot9 (hOH : OneHotAt9 env j) :
    ∀ (l : List ℕ), (∀ i ∈ l, i ∈ statesX9) → l.Nodup →
      evalQX (selS (F := ℚ) l) env = if j ∈ l then 1 else 0
  | [], _, _ => by simp [selS, CoeffExpr.sumList, evalQX]
  | a :: l, hl, hnd => by
      have ih := selS_onehot9 hOH l (fun i hi => hl i (by simp [hi])) (List.nodup_cons.mp hnd).2
      have ha := hOH a (hl a (by simp))
      have hsel : evalQX (selS (F := ℚ) (a :: l)) env = env.trace a + evalQX (selS (F := ℚ) l) env := by
        simp [selS, CoeffExpr.sumList, evalQX, cc]
      rw [hsel, ih, ha]
      by_cases hj : a = j
      · subst hj
        have : a ∉ l := (List.nodup_cons.mp hnd).1
        simp [this]
      · by_cases hjl : j ∈ l
        · simp [hj, hjl]
        · simp [hj, hjl, Ne.symm hj]

theorem act_val9 (hOH : OneHotAt9 env j) {S : SlotX ℚ} (hS : S ∈ (slotsX9 : List (SlotX ℚ)))
    {x : EntX ℚ} (hx : x ∈ S.ents) :
    evalQX x.act env = (if j ∈ x.states then 1 else 0) * evalQX x.extra env := by
  have hok := slotsX9_states_ok S hS x hx
  simp only [EntX.act, evalQX, selS_onehot9 hOH x.states hok.1 hok.2]

theorem act_bool9 (hB : BaseHoldsX9 env) (hOH : OneHotAt9 env j) {S : SlotX ℚ}
    (hS : S ∈ (slotsX9 : List (SlotX ℚ))) :
    ∀ x ∈ S.ents, evalQX x.act env = 0 ∨ evalQX x.act env = 1 := by
  intro x hx
  rw [act_val9 hOH hS hx]
  split_ifs
  · rw [one_mul]; exact extra_bool9 hB S hS x hx
  · left; rw [zero_mul]

theorem act_zero9 (hOH : OneHotAt9 env j) {S : SlotX ℚ} (hS : S ∈ (slotsX9 : List (SlotX ℚ)))
    {x : EntX ℚ} (hx : x ∈ S.ents) (hj : j ∉ x.states) : evalQX x.act env = 0 := by
  rw [act_val9 hOH hS hx, if_neg hj, zero_mul]

theorem act_pairwise9 (hOH : OneHotAt9 env j) {S : SlotX ℚ} (hS : S ∈ (slotsX9 : List (SlotX ℚ))) :
    S.ents.Pairwise fun x y => evalQX x.act env * evalQX y.act env = 0 := by
  have hd := List.pairwise_map.mp (slotsX9_states_disj S hS)
  refine List.Pairwise.imp_of_mem ?_ hd
  intro x y hx hy hxy
  by_cases hj : j ∈ x.states
  · rw [act_zero9 hOH hS hy (hxy j hj), mul_zero]
  · rw [act_zero9 hOH hS hx hj, zero_mul]

/-- The `pr` column's value at a twin row: `s5·β·(1−z1) + s10L + s10S·(1−z1)`. -/
theorem prX_val9 (hB : BaseHoldsX9 env) :
    env.trace prX = env.trace 5 * env.trace betaX * (1 - env.trace z1X) + env.trace sS10L +
      env.trace sS10S * (1 - env.trace z1X) := by
  have a := arith_of_base9 hB (g := prGateX9) (by decide +kernel)
  simp only [prGateX9, prGateX, prodL, List.foldr, cc, notC, evalQX, Rat.cast_one] at a
  linear_combination a

theorem prX_zero9 (hB : BaseHoldsX9 env) (hOH : OneHotAt9 env j) (h5 : j ≠ 5) (h12 : j ≠ sS10L)
    (hS : j ≠ sS10S) : env.trace prX = 0 := by
  have e5 : env.trace 5 = 0 := by rw [hOH 5 (by decide +kernel)]; simp [Ne.symm h5]
  have e12 : env.trace sS10L = 0 := by rw [hOH sS10L (by decide +kernel)]; simp [Ne.symm h12]
  have eS : env.trace sS10S = 0 := by rw [hOH sS10S (by decide +kernel)]; simp [Ne.symm hS]
  rw [prX_val9 hB, e5, e12, eS]; ring

theorem prX_bool9 (hB : BaseHoldsX9 env) (hOH : OneHotAt9 env j) :
    env.trace prX = 0 ∨ env.trace prX = 1 := by
  have hβ := colBool9 hB (i := betaX) (by decide +kernel)
  have hz := colBool9 hB (i := z1X) (by decide +kernel)
  have e5 : env.trace 5 = if 5 = j then 1 else 0 := hOH 5 (by decide +kernel)
  have e12 : env.trace sS10L = if sS10L = j then 1 else 0 := hOH sS10L (by decide +kernel)
  have eS : env.trace sS10S = if sS10S = j then 1 else 0 := hOH sS10S (by decide +kernel)
  rw [prX_val9 hB, e5, e12, eS]
  rcases hβ with hβ | hβ <;> rcases hz with hz | hz <;> by_cases h5 : 5 = j <;>
    by_cases h12 : sS10L = j <;> by_cases hS : sS10S = j <;>
    first
    | (exfalso; simp only [sS10L, sS10S] at h12 hS; omega)
    | simp_all [sS10L, sS10S]

theorem pr2X_zero9 (hB : BaseHoldsX9 env) (hOH : OneHotAt9 env j) (h5 : j ≠ 5) : env.trace pr2X = 0 := by
  have a := arith_of_base9 hB (g := pr2GateX) (by decide +kernel)
  have e5 : env.trace 5 = 0 := by rw [hOH 5 (by decide +kernel)]; simp [Ne.symm h5]
  simp only [pr2GateX, prodL, List.foldr, cc, kbE, evalQX, Rat.cast_one, e5] at a
  linear_combination a

theorem pr2X_bool9 (hB : BaseHoldsX9 env) (hOH : OneHotAt9 env j) :
    env.trace pr2X = 0 ∨ env.trace pr2X = 1 := by
  have a := arith_of_base9 hB (g := pr2GateX) (by decide +kernel)
  have hβ := colBool9 hB (i := betaX) (by decide +kernel)
  have h5 : env.trace 5 = 0 ∨ env.trace 5 = 1 := by
    rw [hOH 5 (by decide +kernel)]; split_ifs <;> simp
  have k1 := kb_bool9 hB (h := xFtth) (by decide) (by decide)
  have k2 := kb_bool9 hB (h := xFttt) (by decide) (by decide)
  simp only [pr2GateX, prodL, List.foldr, cc, kbE, evalQX, Rat.cast_one] at a
  have : env.trace pr2X = env.trace 5 * (env.trace betaX * (env.trace (kbX xFtth) *
      (env.trace (kbX xFttt) * 1))) := by linear_combination a
  rw [this]
  rcases hβ with h | h <;> rcases h5 with h' | h' <;> rcases k1 with k | k <;> rcases k2 with k' | k' <;>
    simp [h, h', k, k']

theorem pairF_bool9 (hB : BaseHoldsX9 env) (hOH : OneHotAt9 env j) {S : SlotX ℚ}
    (hS : S ∈ (slotsX9 : List (SlotX ℚ))) : pairFX env S = 0 ∨ pairFX env S = 1 := by
  simp only [slotsX9, List.mem_cons, List.not_mem_nil, or_false] at hS
  rcases hS with rfl | rfl | rfl | rfl
  · left; rfl
  · left; rfl
  · exact prX_bool9 hB hOH
  · exact pr2X_bool9 hB hOH

theorem pairF_act9 (hB : BaseHoldsX9 env) (hOH : OneHotAt9 env j) {S : SlotX ℚ}
    (hS : S ∈ (slotsX9 : List (SlotX ℚ))) :
    ∀ x ∈ S.ents, pairFX env S * evalQX x.act env = 0 := by
  intro x hx
  by_cases hj : j ∈ x.states
  · have hnp := slotsX9_pair_disj S hS x hx j hj
    have hS' := hS
    simp only [slotsX9, List.mem_cons, List.not_mem_nil, or_false] at hS'
    rcases hS' with rfl | rfl | rfl | rfl
    · simp [pairFX, slot0X9, extSlot, ChipHX.slot0X]
    · simp [pairFX, slot1X9, extSlot, ChipHX.slot1X]
    · have h5 : j ≠ 5 := fun h => hnp (by simp [slot2X9, extSlot, ChipHX.slot2X, h])
      have h12 : j ≠ sS10L := fun h => hnp (by simp [slot2X9, extSlot, ChipHX.slot2X, h, sS10L])
      have hS : j ≠ sS10S := fun h => hnp (by simp [slot2X9, extSlot, h])
      simp only [pairFX, slot2X9, extSlot, ChipHX.slot2X]
      rw [prX_zero9 hB hOH h5 h12 hS, zero_mul]
    · have h5 : j ≠ 5 := fun h => hnp (by simp [slot3X9, extSlot, ChipHX.slot3X, h])
      simp only [pairFX, slot3X9, extSlot, ChipHX.slot3X]
      rw [pr2X_zero9 hB hOH h5, zero_mul]
  · rw [act_zero9 hOH hS hx hj, mul_zero]

end Row

/-! ## 3. The row term of a balance -/

section Term
variable {F K : Type} [Field F] [Field K] [Algebra F K] [DecidableEq F] (δ : F)
  [Fact (¬ IsSquare (algebraMap F K δ))] (b : Basis (Fin 3) F K)

local notation "𝕂′" => Quad (algebraMap F K δ)

/-- The `𝕂′` term of a twin row into balance `bl`: `Σ_S actB · inv′` over `slotsX9`. -/
def termQX9 (eF : Env F) (bl : Bal) : 𝕂′ :=
  ((slotsX9 : List (SlotX ℚ)).map fun S =>
    algebraMap F 𝕂′ (evalQX (S.actB bl) eF) * invQX δ (gatherEnv b eF) S).sum

/-- **A twin row's balance term is the reciprocal sum of its consumed records.** -/
theorem termQX9_row {eF : Env F} {j : ℕ} (hB : BaseHoldsX9 eF) (hOH : OneHotAt9 eF j)
    (hg : ∀ S ∈ (slotsX9 : List (SlotX ℚ)), Q.val δ (slotGateQX F δ (castSlotX S)) (gatherEnv b eF) eF = 0)
    (hden : ∀ S ∈ (slotsX9 : List (SlotX ℚ)), pairFX eF S = 1 →
      pairDaX δ (gatherEnv b eF) eF S ≠ 0 ∧ pairDbX δ (gatherEnv b eF) eF S ≠ 0)
    (bl : Bal) :
    termQX9 δ b eF bl = ((consQX9 eF bl).map fun r => (DX δ (gatherEnv b eF) eF r)⁻¹).sum := by
  set eK := gatherEnv b eF
  rw [termQX9, consQX9, map_flatMap_sum]
  congr 1
  refine List.map_congr_left fun S hS => ?_
  have hcore := slot_core S.ents (fun x => evalQX x.act eF) (fun x => DX δ eK eF x.rcd)
    (fun x => decide (x.bal = bl)) (invQX δ eK S) (pairFX eF S) (pairDaX δ eK eF S) (pairDbX δ eK eF S)
    (act_bool9 hB hOH hS) (act_pairwise9 hOH hS) (pairF_bool9 hB hOH hS) (pairF_act9 hB hOH hS)
    (by rw [← slotGateQX_val_spec]; exact hg S hS) (hden S hS)
  rw [evalQX_actB, map_add, add_mul, hcore.1, List.map_append, List.sum_append, List.map_map]
  congr 1
  unfold pairRecsB
  have h2 := hcore.2
  unfold pairFX pairDaX pairDbX at h2
  cases hp : S.pair with
  | none => simp
  | some q =>
    obtain ⟨fl, a, c, b'⟩ := q
    rw [hp] at h2
    simp only at h2 ⊢
    by_cases hb' : b' = bl
    · have hpf : pairFX eF S = eF.trace fl := by simp [pairFX, hp]
      rw [if_pos hb', hpf]
      change _ * invQX δ eK S = _
      rw [h2]
      by_cases hf : eF.trace fl = 1
      · simp [hb', hf]
      · simp [hf]
    · simp [hb']

end Term

/-! ## 4. The accumulator telescope -/

section Bal
variable {F K : Type} [Field F] [Field K] [Algebra F K] [DecidableEq F] (δ : F)
  [Fact (¬ IsSquare (algebraMap F K δ))] (b : Basis (Fin 3) F K)
open Compute.LogUp (limbVal Slot)

local notation "𝕂′" => Quad (algebraMap F K δ)

/-- The accumulator slots of balance `bl` at the twin slots. -/
def slotsB9 (bl : Bal) (im : Bool) : List (Slot ℚ) :=
  (slotsX9 : List (SlotX ℚ)).map fun S => ⟨S.actB bl, if im then S.invIm else S.inv⟩

theorem accRe_sub9 (bl : Bal) :
    ∀ g ∈ (accGatesX (slotsB9 bl false) (balCols bl).1 (balCols bl).2.1 : List (CoeffExpr ℚ)),
      g ∈ (baseGatesHX9 : List (CoeffExpr ℚ)) := by
  intro g hg
  refine List.mem_append_left _ (List.mem_append_right _ ?_)
  simp only [accGatesHX9, List.mem_append]
  cases bl
  · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl hg))))
  · exact Or.inl (Or.inl (Or.inl (Or.inr hg)))
  · exact Or.inl (Or.inr hg)

theorem accIm_sub9 (bl : Bal) :
    ∀ g ∈ (accGatesX (slotsB9 bl true) (balCols bl).2.2.1 (balCols bl).2.2.2 : List (CoeffExpr ℚ)),
      g ∈ (baseGatesHX9 : List (CoeffExpr ℚ)) := by
  intro g hg
  refine List.mem_append_left _ (List.mem_append_right _ ?_)
  simp only [accGatesHX9, List.mem_append]
  cases bl
  · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hg))))
  · exact Or.inl (Or.inl (Or.inr hg))
  · exact Or.inr hg

/-- A twin row's `𝕂′` balance term is the pair (Re accumulator term, Im accumulator term). -/
theorem termQX9_eq (eF : Env F) (bl : Bal) :
    termQX9 δ b eF bl = Quad.mk _ (termValX b (slotsB9 bl false) eF) (termValX b (slotsB9 bl true) eF) := by
  simp only [termValX, slotsB9, List.map_map, Function.comp_def, Bool.false_eq_true, if_false, if_true]
  rw [mk_list_sumX, termQX9]
  congr 1
  refine List.map_congr_left fun S _ => ?_
  rw [invQX, aMFX, Quad.mk_smul, Algebra.smul_def, Algebra.smul_def]
  rfl

end Bal

/-! ## 5. The accepted twin chip -/

section Chip
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq F]
  {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F) (b : Basis (Fin 3) F K) (δ : F)
  [Fact (¬ IsSquare (algebraMap F K δ))]
  (chalV pubVal : ℕ → F) (orbit : StrictOrbitDomain F 3 h)
  (P : Fin (computeChipVCLHX9 hn nodes b δ chalV pubVal orbit).rap.w → F[X])
open Compute.LogUp (limbVal)

local notation "𝕂′" => Quad (algebraMap F K δ)
local notation "EN9" => envsN9 hn nodes orbit chalV pubVal P

/-- Base gates at every row of an accepted twin trace, read through `permX9` (generic field). -/
theorem baseX9_of_satG (hsat : (computeChipVCLHX9 hn nodes b δ chalV pubVal orbit).rap.Satisfies P)
    (x : F) (hx : x ∈ rowNodeSet nodes) :
    BaseHoldsX9 (Env.viaPerm permX9 (Reify.envOfTrace P orbit.ω x chalV pubVal)) := by
  intro t ht
  have h0 := computeChipVCLHX9_sat_twin hn nodes b δ chalV pubVal orbit P hsat x hx
    (mapC (fun q : ℚ => (q : F)) t)
    (List.mem_append_left _ (List.mem_append_left _ (List.mem_map_of_mem ht)))
  rwa [eval_mapC_cast, ← RapWalkJ8.evalQX_eq] at h0

/-- The twin slot pairs vanish at every row of an accepted trace. -/
theorem slotX9_of_sat (hsat : (computeChipVCLHX9 hn nodes b δ chalV pubVal orbit).rap.Satisfies P)
    (x : F) (hx : x ∈ rowNodeSet nodes) (S : SlotX ℚ) (hS : S ∈ (slotsX9 : List (SlotX ℚ))) :
    Q.val δ (slotGateQX F δ (castSlotX S))
      (gatherEnv b (Env.viaPerm permX9 (Reify.envOfTrace P orbit.ω x chalV pubVal)))
      (Env.viaPerm permX9 (Reify.envOfTrace P orbit.ω x chalV pubVal)) = 0 := by
  have hall := computeChipVCLHX9_sat_twin hn nodes b δ chalV pubVal orbit P hsat x hx
  have hS' : castSlotX S ∈ (slotsX9 : List (SlotX F)) := by
    rw [← slotsX9_cast]; exact List.mem_map_of_mem hS
  have hz : Q.IsZero (slotGateQX F δ (castSlotX S))
      (gatherEnv b (Env.viaPerm permX9 (Reify.envOfTrace P orbit.ω x chalV pubVal)))
      (Env.viaPerm permX9 (Reify.envOfTrace P orbit.ω x chalV pubVal)) :=
    (Compute.TowerD.qGates_iff b (isCoordEnv_gather b _) _).mp fun g hg =>
      hall g (List.mem_append_left _ (List.mem_append_right _ (List.mem_flatMap.mpr
        ⟨_, List.mem_map_of_mem hS', hg⟩)))
  exact (Q.isZero_iff δ _ _ _).mp hz

/-- **The extraction context** of the twin compute balances.  `oh` (a row is one-hot over the 20 twin
states) is a FIELD, supplied elsewhere. -/
structure BCtx9 : Prop where
  hc : 20 < ringChar F
  hsat : RAP.SatisfiesWithPreprocessing (computeChipVCLHX9 hn nodes b δ chalV pubVal orbit) P
  hinj : Function.Injective nodes
  hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω
  oh : ∀ r < n, ∃ j ∈ statesX9, OneHotAt9 (envsN9 hn nodes orbit chalV pubVal P r) j

variable {hn nodes b δ chalV pubVal orbit P}
  (C : BCtx9 hn nodes b δ chalV pubVal orbit P)
include C

theorem envsN9_ltB (k : ℕ) (hk : k < n) :
    EN9 k = Env.viaPerm permX9 (rEF nodes chalV pubVal orbit P ⟨k, hk⟩) := by
  simp [envsN9, TeleC.envsN, hk]

theorem baseB9 {r : ℕ} (hr : r < n) : BaseHoldsX9 (EN9 r) := by
  rw [envsN9_ltB C r hr]
  exact baseX9_of_satG hn nodes b δ chalV pubVal orbit P C.hsat.1 _ (mem_rowNodeSet nodes _)

theorem slotB9 {r : ℕ} (hr : r < n) (S : SlotX ℚ) (hS : S ∈ (slotsX9 : List (SlotX ℚ))) :
    Q.val δ (slotGateQX F δ (castSlotX S)) (gatherEnv b (EN9 r)) (EN9 r) = 0 := by
  rw [envsN9_ltB C r hr]
  exact slotX9_of_sat hn nodes b δ chalV pubVal orbit P C.hsat.1 _ (mem_rowNodeSet nodes _) S hS

theorem masksB9 {r : ℕ} (hr : r < n) :
    (EN9 r).trace firstX = (if r = 0 then 1 else 0) ∧ (EN9 r).trace lastX = (if r = n - 1 then 1 else 0) := by
  have hbind := C.hsat.2
  have hw : (computeChipVCLHX9 hn nodes b δ chalV pubVal orbit).rap.w = 137 := rfl
  have h0 : P ⟨17, by rw [hw]; omega⟩ = firstRowMask nodes := hbind ⟨0, by show 0 < 2; omega⟩
  have h1 : P ⟨18, by rw [hw]; omega⟩ = lastRowMask hn nodes := hbind ⟨1, by show 1 < 2; omega⟩
  rw [envsN9_ltB C r hr]
  show (rEF nodes chalV pubVal orbit P ⟨r, hr⟩).trace (permX9 17) = _ ∧
    (rEF nodes chalV pubVal orbit P ⟨r, hr⟩).trace (permX9 18) = _
  rw [permX9_fixes_pre 17 (by norm_num), permX9_fixes_pre 18 (by norm_num)]
  rw [envOfTrace_trace P _ _ _ _ (show 17 < _ by rw [hw]; omega),
    envOfTrace_trace P _ _ _ _ (show 18 < _ by rw [hw]; omega), h0, h1,
    firstRowMask_eval nodes C.hinj ⟨r, hr⟩, lastRowMask_eval hn nodes C.hinj ⟨r, hr⟩]
  refine ⟨rfl, ?_⟩
  by_cases hi : r = n - 1
  · rw [if_pos (Fin.ext hi), if_pos hi]
  · rw [if_neg (fun h => hi (congrArg Fin.val h)), if_neg hi]

theorem shiftB9 {r : ℕ} (hr : r + 1 < n) : (EN9 r).traceNext = (EN9 (r + 1)).trace := by
  funext c
  rw [envsN9_ltB C r (by omega), envsN9_ltB C (r + 1) hr]
  exact traceNext_eq nodes orbit P chalV pubVal C.hadj ⟨r, by omega⟩ hr (permX9 c)

theorem pubB9 (r : ℕ) : (EN9 r).pub = pubVal := by
  unfold envsN9 TeleC.envsN; split_ifs <;> rfl

theorem chalB9 (r : ℕ) : (EN9 r).chal = chalV := by
  unfold envsN9 TeleC.envsN; split_ifs <;> rfl

theorem accB9_rows (slots : List (Compute.LogUp.Slot ℚ)) (accBase pubBase : ℕ)
    (hsub : ∀ g ∈ (accGatesX slots accBase pubBase : List (CoeffExpr ℚ)), g ∈ (baseGatesHX9 : List (CoeffExpr ℚ))) :
    ∑ i ∈ Finset.range n, termValX b slots (EN9 i) = limbVal b pubVal pubBase := by
  rw [accX_rows b slots accBase pubBase n hn EN9 (fun i hi g hg => baseB9 C hi g (hsub g hg))
    (fun i hi => shiftB9 C hi) (by rw [(masksB9 C hn).1]; simp)
    (fun i hi => by rw [(masksB9 C (by omega)).2]; simp; omega)
    (by rw [(masksB9 C (by omega)).2]; simp), pubB9 C]

/-- **The compute side of the twin handle-class balances**: on an accepted `computeChipVCLHX9` trace
(one-hot rows), for each balance `bl ∈ {x, p, s}` the reciprocal sum of the records the rows consume into
`bl` is the public `(Re ρ_bl, Im ρ_bl)` — given nonzero pair denominators. -/
theorem compute_balanceX9
    (hden : ∀ r < n, ∀ S ∈ (slotsX9 : List (SlotX ℚ)), pairFX (EN9 r) S = 1 →
      pairDaX δ (gatherEnv b (EN9 r)) (EN9 r) S ≠ 0 ∧ pairDbX δ (gatherEnv b (EN9 r)) (EN9 r) S ≠ 0)
    (bl : Bal) :
    ∑ i ∈ Finset.range n, ((consQX9 (EN9 i) bl).map fun r => (DX δ (gatherEnv b (EN9 i)) (EN9 i) r)⁻¹).sum =
      Quad.mk (algebraMap F K δ) (limbVal b pubVal (balCols bl).2.1) (limbVal b pubVal (balCols bl).2.2.2) := by
  have hrow : ∀ i ∈ Finset.range n,
      ((consQX9 (EN9 i) bl).map fun r => (DX δ (gatherEnv b (EN9 i)) (EN9 i) r)⁻¹).sum =
        Quad.mk (algebraMap F K δ) (termValX b (slotsB9 bl false) (EN9 i))
          (termValX b (slotsB9 bl true) (EN9 i)) := by
    intro i hi
    have hi' := Finset.mem_range.mp hi
    obtain ⟨j, -, hj⟩ := C.oh i hi'
    rw [← termQX9_eq, termQX9_row δ b (baseB9 C hi') hj
      (fun S hS => slotB9 C hi' S hS) (hden i hi') bl]
  rw [Finset.sum_congr rfl hrow, mk_fsumX, accB9_rows C _ _ _ (accRe_sub9 bl),
    accB9_rows C _ _ _ (accIm_sub9 bl)]


/-! ## 6. Record lengths, the `compress` form, the request list -/

omit C in
theorem slotsX9_len : ∀ S ∈ (slotsX9 : List (SlotX ℚ)),
    (S.ents.all fun x => decide (x.rcd.length ≤ mOf x.bal)) = true ∧
    (match S.pair with
     | some (_, a, c, bl) => decide (a.length ≤ mOf bl ∧ c.length ≤ mOf bl)
     | none => true) = true := by
  decide +kernel

omit C in
/-- **Every record a twin row consumes into `bl` has length `≤ mOf bl`.** -/
theorem consQX9_len (eF : Env F) (bl : Bal) : ∀ r ∈ consQX9 eF bl, r.length ≤ mOf bl := by
  intro r hr
  obtain ⟨S, hS, hr0⟩ := List.mem_flatMap.mp hr
  obtain ⟨hents, hpair⟩ := slotsX9_len S hS
  rcases List.mem_append.mp hr0 with hr1 | hr2
  · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hr1
    have hx1 := (List.mem_filter.mp hx).1
    have hb := of_decide_eq_true (List.mem_filter.mp hx1).2
    have := of_decide_eq_true (List.all_eq_true.mp hents x (List.mem_filter.mp hx1).1)
    rw [← hb]
    exact this
  · unfold pairRecsB at hr2
    cases hp : S.pair with
    | none => rw [hp] at hr2; simp at hr2
    | some q =>
      obtain ⟨fl, a, c, b'⟩ := q
      rw [hp] at hr2 hpair
      simp only at hr2 hpair
      have := of_decide_eq_true hpair
      by_cases hc : b' = bl ∧ eF.trace fl = 1
      · rw [if_pos hc] at hr2
        obtain ⟨rfl, -⟩ := hc
        rcases List.mem_pair.mp hr2 with rfl | rfl
        · exact this.1
        · exact this.2
      · rw [if_neg hc] at hr2; simp at hr2

theorem coinsCQ_EN9 (r : ℕ) : coinsCQ δ (gatherEnv b (EN9 r)) = coinsCV b δ chalV := by
  unfold coinsCQ coinsCV
  simp only [Compute.TowerD.gatherEnv, chalB9 C]

variable [Fintype K]

/-- **`compute_balanceX9` in `compress` form**, at the coins read off the challenge vector. -/
theorem compute_balanceX9_keys
    (hden : ∀ r < n, ∀ S ∈ (slotsX9 : List (SlotX ℚ)), pairFX (EN9 r) S = 1 →
      pairDaX δ (gatherEnv b (EN9 r)) (EN9 r) S ≠ 0 ∧ pairDbX δ (gatherEnv b (EN9 r)) (EN9 r) S ≠ 0)
    (bl : Bal) :
    ∑ i ∈ Finset.range n, ((consQX9 (EN9 i) bl).map fun r =>
        (compress (coinsCV b δ chalV) (liftRec (L := 𝕂′) (keyX (K := K) (mOf bl) r (EN9 i))))⁻¹).sum =
      Quad.mk (algebraMap F K δ) (limbVal b pubVal (balCols bl).2.1) (limbVal b pubVal (balCols bl).2.2.2) := by
  rw [← compute_balanceX9 C hden bl]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  refine List.map_congr_left fun r hr => ?_
  rw [denQX_val δ _ _ r (mOf bl) (consQX9_len _ bl r hr), coinsCQ_EN9 C]

omit C in
theorem pair_mem_consQX9 (eF : Env F) {S : SlotX ℚ} (hS : S ∈ (slotsX9 : List (SlotX ℚ)))
    {fl : ℕ} {a c : List RE} {bl : Bal} (hp : S.pair = some (fl, a, c, bl)) (hf : eF.trace fl = 1) :
    a ∈ consQX9 eF bl ∧ c ∈ consQX9 eF bl := by
  have hpr : pairRecsB eF bl S = [a, c] := by
    unfold pairRecsB; rw [hp]; simp [hf]
  refine ⟨List.mem_flatMap.mpr ⟨S, hS, List.mem_append_right _ ?_⟩,
    List.mem_flatMap.mpr ⟨S, hS, List.mem_append_right _ ?_⟩⟩ <;> rw [hpr] <;> simp

omit C in
theorem sum_flatMap_range9 {M : Type} [AddCommMonoid M] (f : ℕ → List M) :
    ∀ n, ((List.range n).flatMap f).sum = ∑ i ∈ Finset.range n, (f i).sum
  | 0 => by simp
  | n + 1 => by
    rw [List.range_succ, List.flatMap_append, List.sum_append, sum_flatMap_range9 f n, Finset.sum_range_succ]
    simp

/-- **`hden` of `compute_balanceX9` is discharged** by the nonzero denominators of the request lists. -/
theorem hden_of_reqs9
    (hne : ∀ bl, ∀ r ∈ compReqsX9 (K := K) hn nodes orbit chalV pubVal P bl,
      compress (coinsCV b δ chalV) (liftRec (L := 𝕂′) r) ≠ 0) :
    ∀ r < n, ∀ S ∈ (slotsX9 : List (SlotX ℚ)), pairFX (EN9 r) S = 1 →
      pairDaX δ (gatherEnv b (EN9 r)) (EN9 r) S ≠ 0 ∧ pairDbX δ (gatherEnv b (EN9 r)) (EN9 r) S ≠ 0 := by
  intro i hi S hS hf
  unfold pairFX at hf
  unfold pairDaX pairDbX
  cases hp : S.pair with
  | none => rw [hp] at hf; exact absurd hf (by simp)
  | some q =>
    obtain ⟨fl, a, c, bl⟩ := q
    rw [hp] at hf
    simp only at hf ⊢
    obtain ⟨ha, hc⟩ := pair_mem_consQX9 (EN9 i) hS hp hf
    have hmem : ∀ r ∈ consQX9 (EN9 i) bl, keyX (K := K) (mOf bl) r (EN9 i) ∈
        compReqsX9 (K := K) hn nodes orbit chalV pubVal P bl := fun r hr =>
      List.mem_flatMap.mpr ⟨i, List.mem_range.mpr hi, List.mem_map_of_mem hr⟩
    refine ⟨?_, ?_⟩
    · rw [denQX_val δ _ _ a (mOf bl) (consQX9_len _ bl a ha), coinsCQ_EN9 C]
      exact hne bl _ (hmem a ha)
    · rw [denQX_val δ _ _ c (mOf bl) (consQX9_len _ bl c hc), coinsCQ_EN9 C]
      exact hne bl _ (hmem c hc)

/-- **The compute side of each twin handle-class balance, in list form**, `hden`-free. -/
theorem compReqsX9_sum
    (hne : ∀ bl, ∀ r ∈ compReqsX9 (K := K) hn nodes orbit chalV pubVal P bl,
      compress (coinsCV b δ chalV) (liftRec (L := 𝕂′) r) ≠ 0)
    (bl : Bal) :
    ((compReqsX9 (K := K) hn nodes orbit chalV pubVal P bl).map fun r =>
        (compress (coinsCV b δ chalV) (liftRec (L := 𝕂′) r))⁻¹).sum =
      Quad.mk (algebraMap F K δ) (limbVal b pubVal (balCols bl).2.1) (limbVal b pubVal (balCols bl).2.2.2) := by
  rw [← compute_balanceX9_keys C (hden_of_reqs9 C hne) bl, compReqsX9, List.map_flatMap, sum_flatMap_range9]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [List.map_map]
  rfl

end Chip

/-! ## 7. The consumed records are `activeX9`'s, per balance -/

section Active
variable {p : ℕ} [Fact p.Prime]
open Nock.NockVMROM.Thm54.VclL.Handle.RowSemChipX (pairRecsX reVal)
open Nock.NockVMROM.Thm54.VclL.Handle.RowSemChipX9 (activeX9)

/-- **`consQX9` is `activeX9` filtered by balance** (records read as `ZMod.val` values). -/
theorem consQX9_activeX9 (env : Env (ZMod p)) (bl : Bal) :
    ((activeX9 env).filter fun r => decide (r.2 = bl)).map (·.1) =
      (consQX9 env bl).map (·.map (reVal env)) := by
  unfold activeX9 consQX9
  rw [List.filter_flatMap, List.map_flatMap, List.map_flatMap]
  congr 1
  funext S
  rw [List.filter_append, List.map_append, List.map_append]
  congr 1
  · rw [List.filter_map, List.map_map, List.map_map, List.filter_filter, List.filter_filter]
    congr 1
    exact List.filter_congr fun x _ => by simp [Function.comp, Bool.and_comm]
  · unfold pairRecsX pairRecsB
    cases hp : S.pair with
    | none => simp
    | some q =>
      obtain ⟨fl, a, c, b'⟩ := q
      simp only
      by_cases hf : env.trace fl = 1 <;> by_cases hb : b' = bl <;> simp [hf, hb]

end Active

/-! ## 8. The served records at the twin -/

section Served
open Nock.NockVMROM.Thm54.VclL.Handle.ServedJ8 (liftP BalJ8 ProvP den_prov_ne_of_out)
open Nock.NockVMROM.Thm54.VclL.Handle.RowSemChipX9 (activeX9)
open Nock.NockVMROM.Thm54.VclL.Handle.RowSemChipX (reVal)
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K]
  {h n : ℕ} {hn : 0 < n} {nodes : Fin n → ZMod p} {b : Basis (Fin 3) (ZMod p) K} {δ : ZMod p}
  [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))] [DecidableEq (Quad (algebraMap (ZMod p) K δ))]
  {chalV pubVal : ℕ → ZMod p} {orbit : StrictOrbitDomain (ZMod p) 3 h}
  {P : Fin (computeChipVCLHX9 hn nodes b δ chalV pubVal orbit).rap.w → (ZMod p)[X]}

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)
local notation "EN9" => envsN9 hn nodes orbit chalV pubVal P
local notation "CV" => coinsCV b δ chalV

theorem slotsX9_tags : ∀ S ∈ (slotsX9 : List (SlotX ℚ)),
    ((S.ents.all fun x => x.rcd.all fun e => match e with | .k c => decide (c ≤ 5) | .col _ => true) = true) ∧
    (match S.pair with
     | some (_, a, c, _) => (a ++ c).all (fun e => match e with | .k c => decide (c ≤ 5) | .col _ => true)
     | none => true) = true := by
  decide +kernel

theorem consQX9_tags {F : Type} [Field F] [DecidableEq F] (eF : Env F) (bl : Bal) :
    ∀ r ∈ consQX9 eF bl, ∀ t, RE.k t ∈ r → t ≤ 5 := by
  intro r hr t ht
  obtain ⟨S, hS, hr0⟩ := List.mem_flatMap.mp hr
  obtain ⟨hents, hpair⟩ := slotsX9_tags S hS
  have key : ∀ l : List RE, (l.all fun e => match e with | .k c => decide (c ≤ 5) | .col _ => true) = true →
      ∀ t, RE.k t ∈ l → t ≤ 5 := by
    intro l hl t ht
    have := List.all_eq_true.mp hl _ ht
    simpa using this
  rcases List.mem_append.mp hr0 with hr1 | hr2
  · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hr1
    have hx1 := (List.mem_filter.mp (List.mem_filter.mp hx).1).1
    exact key _ (List.all_eq_true.mp hents x hx1) t ht
  · unfold pairRecsB at hr2
    cases hp : S.pair with
    | none => rw [hp] at hr2; simp at hr2
    | some q =>
      obtain ⟨fl, a, c, b'⟩ := q
      rw [hp] at hr2 hpair
      simp only at hr2 hpair
      by_cases hc : b' = bl ∧ eF.trace fl = 1
      · rw [if_pos hc] at hr2
        rcases List.mem_pair.mp hr2 with rfl | rfl
        · exact key _ hpair t (by simp [ht])
        · exact key _ hpair t (by simp [ht])
      · rw [if_neg hc] at hr2; simp at hr2

theorem reVal_lt9 (hp5 : 5 < p) (env : Env (ZMod p)) (bl : Bal) :
    ∀ r ∈ consQX9 env bl, ∀ e ∈ r.map (reVal env), e < p := by
  intro r hr e he
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp he
  cases x with
  | col i => exact ZMod.val_lt _
  | k c => exact lt_of_le_of_lt (consQX9_tags env bl r hr c hx) hp5

/-- The request list of a balance at the twin: the compute's and the other consumers', lifted. -/
def reqsJ9 (ext : (bl : Bal) → List (Fin (mOf bl) → K)) (bl : Bal) : List (Fin (mOf bl) → 𝕂′) :=
  (compReqsX9 (K := K) hn nodes orbit chalV pubVal P bl ++ ext bl).map (liftRec (L := 𝕂′))

/-- **Every consumed twin record satisfies the providers' obligation `Φ`.**  On an accepted
`computeChipVCLHX9` trace (`BCtx9`), under the balance identity, outside each balance's weighted IO
failure event at the compute coins, with consumer counts `< p` and the providers' obligation, every record
any twin row consumes satisfies `Φ`.  (`hp4` is kept for signature compatibility; the twin's `TAG_ax`
constant is `5`, and `5 < p` comes from `C.hc`.) -/
theorem servedP_of_balancesJ9 [CharP 𝕂′ p] (C : BCtx9 hn nodes b δ chalV pubVal orbit P) (hp4 : 4 < p)
    {provs : (bl : Bal) → List ((Fin (mOf bl) → K) × K)} {ext : (bl : Bal) → List (Fin (mOf bl) → K)}
    (hbal : BalJ8 (b := b) (δ := δ) (chalV := chalV) (pubVal := pubVal) provs ext)
    (hout : ∀ bl, ((CV).gamma, (CV).pole) ∉
      IOFailureEventW (reqsJ9 (hn := hn) (nodes := nodes) (b := b) (δ := δ) (chalV := chalV)
        (pubVal := pubVal) (orbit := orbit) (P := P) ext bl) (liftP (provs bl)))
    (hcount : ∀ bl, (reqsJ9 (hn := hn) (nodes := nodes) (b := b) (δ := δ) (chalV := chalV)
        (pubVal := pubVal) (orbit := orbit) (P := P) ext bl).length < p)
    {Φ : List ℕ × Bal → Prop}
    (hprov : ∀ bl, ProvP (p := p) (K := K) Φ bl (provs bl)) :
    ∀ r < n, ∀ x ∈ activeX9 (EN9 r), Φ x := by
  have hp5 : 5 < p := by
    have := C.hc
    rw [ZMod.ringChar_zmod_n] at this
    omega
  have hd : ∀ bl, ∀ r ∈ reqsJ9 (hn := hn) (nodes := nodes) (b := b) (δ := δ) (chalV := chalV)
      (pubVal := pubVal) (orbit := orbit) (P := P) ext bl, compress ⟨(CV).gamma, (CV).pole⟩ r ≠ 0 :=
    fun bl => TeleC.den_ne_of_out _ _ _ _ (hout bl)
  have hne : ∀ bl, ∀ r ∈ compReqsX9 (K := K) hn nodes orbit chalV pubVal P bl,
      compress CV (liftRec (L := 𝕂′) r) ≠ 0 :=
    fun bl r hr => hd bl _ (List.mem_map_of_mem (List.mem_append_left _ hr))
  have hserved : ∀ bl, ∀ r ∈ reqsJ9 (hn := hn) (nodes := nodes) (b := b) (δ := δ) (chalV := chalV)
      (pubVal := pubVal) (orbit := orbit) (P := P) ext bl, r ∈ (liftP (provs bl)).map Prod.fst := by
    intro bl
    refine ServeH.served_of_balance (p := p) _ _ _ _ (hd bl)
      (den_prov_ne_of_out _ _ _ _ (hout bl)) ?_ (hcount bl) (hout bl)
    have h1 := compReqsX9_sum C hne bl
    have h2 := hbal bl
    unfold reqsJ9 liftP
    rw [List.map_map, List.map_append, List.sum_append, List.map_map]
    simp only [Function.comp_def] at h1 ⊢
    rw [h1]
    exact h2
  intro i hi x hx
  obtain ⟨l, bl⟩ := x
  have hmem : l ∈ ((activeX9 (EN9 i)).filter fun r => decide (r.2 = bl)).map (·.1) :=
    List.mem_map.mpr ⟨(l, bl), List.mem_filter.mpr ⟨hx, by simp⟩, rfl⟩
  rw [consQX9_activeX9] at hmem
  obtain ⟨rec, hrec, rfl⟩ := List.mem_map.mp hmem
  have hk : keyX (K := K) (mOf bl) rec (EN9 i) ∈
      compReqsX9 (K := K) hn nodes orbit chalV pubVal P bl :=
    List.mem_flatMap.mpr ⟨i, List.mem_range.mpr hi, List.mem_map_of_mem hrec⟩
  obtain ⟨q, hq, hqe⟩ := List.mem_map.mp
    (hserved bl _ (List.mem_map_of_mem (List.mem_append_left _ hk)))
  obtain ⟨q0, hq0, rfl⟩ := List.mem_map.mp hq
  have hkey : q0.1 = keyX (K := K) (mOf bl) rec (EN9 i) := liftRec_inj hqe
  refine hprov bl q0 hq0 _ ?_ (reVal_lt9 hp5 _ bl rec hrec) ?_
  · rw [List.length_map]; exact consQX9_len _ bl rec hrec
  · rw [hkey, DenXJ8.keyX_natKey]

end Served

end

end Nock.NockVMROM.Thm54.VclL.Handle.TeleX9

section Axioms
open Nock.NockVMROM.Thm54.VclL.Handle.TeleX9
#print axioms compute_balanceX9
#print axioms compute_balanceX9_keys
#print axioms compReqsX9_sum
#print axioms consQX9_activeX9
#print axioms servedP_of_balancesJ9
end Axioms
