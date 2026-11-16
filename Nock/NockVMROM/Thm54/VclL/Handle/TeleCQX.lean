/-
  Nock/NockVMROM/Thm54/VclL/Handle/TeleCQX.lean

  **The compute half of the J-8 handle-class
  balances** — the `TeleCQ` pattern at `computeChipVCLHX`.  New module, additive.

  * `castSlotX` / `slotsX_cast`: the `F`-slots of `slotPairsX` are the `ℚ` slots with their extras cast.
  * `slotGateQX_val_spec`: the value of a `𝕂′` slot pair (`Q.val`).
  * Row facts at a one-hot row whose base gates hold (`act_bool`, `act_pairwise`, `pairF_bool`,
    `pairF_act`): activities are `0 / 1`, at most one per slot, the pair flags `pr` / `pr2` are `0 / 1`
    and exclusive with the slot's entries.
  * `termQX_row`: a row's `𝕂′` term into balance `b ∈ {x, p, s}` is `Σ (D r)⁻¹` over the records the
    row consumes into `b` (`consQX b`), `D r = Q.val (denQX r)` at the gathered environment.
  * `accX_rows`: the accumulator telescope at the masks `17 / 18`.
  * **`compute_balanceX`**: on an accepted `computeChipVCLHX` trace (injective `ω`-adjacent nodes,
    `17 < char`), for each balance `b`, `Σ_rows Σ_{consQX b} (D r)⁻¹ = (Re ρ_b, Im ρ_b)` (the publics
    `15/21` export, `18/24` path, `27/30` service) — the compute side of `GoodCJ8`'s three handle-class
    balance equations.  Pair denominators are assumed nonzero (`hden`; the IO event excludes zeros).
  * `consQX_activeX`: `consQX env b` is `RowSemChipX.activeX env` filtered by balance `b` (values as
    `ZMod.val`), so the summed records are exactly those `RecOK` must hold of.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.RapWalkJ8
import Nock.NockVMROM.Thm54.VclL.Handle.TeleCQ

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000

namespace Nock.NockVMROM.Thm54.VclL.Handle.TeleCQX

open Nock Nock.Reified Nock.Framework Nock.Edit Module Polynomial
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler Nock.NockVMROM.Thm54.T0Tower Nock.NockVMROM.Thm54.T0TowerFP
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.MonolithicRAP Nock.Framework.Reify
open Nock.NockVMROM.Thm54.VclL.Compute.TowerD
open Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.ChipH (Hd cc notC selS prodL mapC chalGammaL chalRhoL pubRhoX pubRhoP)
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHQ (sumQ qγH qρH chalGammaIm chalRhoIm pubRhoXIm pubRhoPIm)
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHX
open Nock.NockVMROM.Thm54.VclL.Handle.TeleC (rEF envsN slot_core)
open Nock.NockVMROM.Thm54.VclL.Handle.RapWalkJ8
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP

noncomputable section

/-! ## 1. The slots at `ℚ` and at `F` -/

section Cast
variable {F : Type} [Field F]

def castEntX (x : EntX ℚ) : EntX F := ⟨x.states, mapC (fun q : ℚ => (q : F)) x.extra, x.rcd, x.bal⟩
def castSlotX (S : SlotX ℚ) : SlotX F := ⟨S.inv, S.invIm, S.ents.map castEntX, S.pair, S.pairStates⟩

theorem slotsX_cast : (ChipHX.slotsX (F := ℚ)).map castSlotX = (ChipHX.slotsX (F := F)) := by
  simp [ChipHX.slotsX, slot0X, slot1X, slot2X, slot3X, castSlotX, castEntX, mapC, notC, cc, kcE, kbE]

theorem evalQX_sumList {ι : Type} (l : List ι) (f : ι → CoeffExpr ℚ) (env : Env F) :
    evalQX (CoeffExpr.sumList l f) env = (l.map fun i => evalQX (f i) env).sum := by
  induction l with
  | nil => simp [CoeffExpr.sumList, evalQX]
  | cons a l ih =>
    simp only [CoeffExpr.sumList, List.foldr_cons] at ih ⊢
    simp [evalQX, ih]

theorem castEntX_act (x : EntX ℚ) (eF : Env F) : (castEntX x).act.eval eF = evalQX x.act eF := by
  rw [evalQX_eq]
  simp only [castEntX, EntX.act, CoeffExpr.eval, evalQ, eval_mapC_cast, selS, CoeffExpr.eval_sumList,
    evalQ_sumList, cc, TeleC.evalQ_cc]

theorem castEntX_sumAct (l : List (EntX ℚ)) (eF : Env F) :
    (CoeffExpr.sumList (l.map castEntX) EntX.act).eval eF = (l.map fun x => evalQX x.act eF).sum := by
  rw [CoeffExpr.eval_sumList, List.map_map]
  congr 1
  exact List.map_congr_left fun x _ => castEntX_act x eF

end Cast

/-! ## 2. Values at the `𝕂′` coins -/

section Val
variable {F K : Type} [Field F] [Field K] [Algebra F K] (δ : F) (eK : Env K) (eF : Env F)

local notation "𝕂′" => Quad (algebraMap F K δ)

/-- A record's `𝕂′` denominator. -/
def DX (r : List RE) : 𝕂′ := Q.val δ (denQX F δ r) eK eF

/-- The `𝕂′` inverse of a slot. -/
def invQX (S : SlotX ℚ) : 𝕂′ := Quad.mk _ (eK.trace S.inv) (eK.trace S.invIm)

/-- A slot's pair flag value. -/
def pairFX (S : SlotX ℚ) : F :=
  match S.pair with
  | some (fl, _, _, _) => eF.trace fl
  | none => 0

def pairDaX (S : SlotX ℚ) : 𝕂′ :=
  match S.pair with
  | some (_, a, _, _) => DX δ eK eF a
  | none => 0

def pairDbX (S : SlotX ℚ) : 𝕂′ :=
  match S.pair with
  | some (_, _, c, _) => DX δ eK eF c
  | none => 0

theorem aMFX (x : F) : algebraMap F 𝕂′ x = algebraMap K 𝕂′ (algebraMap F K x) :=
  IsScalarTower.algebraMap_apply F K _ x

/-- **The `𝕂′` slot pair's value.** -/
theorem slotGateQX_val_spec (S : SlotX ℚ) :
    Q.val δ (slotGateQX F δ (castSlotX S)) eK eF =
      invQX δ eK S * ((S.ents.map fun x => algebraMap F 𝕂′ (evalQX x.act eF) * DX δ eK eF x.rcd).sum +
          algebraMap F 𝕂′ (pairFX eF S) * (pairDaX δ eK eF S * pairDbX δ eK eF S)) -
        (algebraMap F 𝕂′ ((S.ents.map fun x => evalQX x.act eF).sum) +
          algebraMap F 𝕂′ (pairFX eF S) * (pairDaX δ eK eF S + pairDbX δ eK eF S)) := by
  have hents : Q.val δ (sumQ F ((castSlotX (F := F) S).ents.map fun x =>
      qmul F δ (qlift F x.act) (denQX F δ x.rcd))) eK eF =
      (S.ents.map fun x => algebraMap F 𝕂′ (evalQX x.act eF) * DX δ eK eF x.rcd).sum := by
    rw [ComputeSatHQ.sumQ_val]
    simp only [castSlotX, List.map_map]
    congr 1
    refine List.map_congr_left fun x _ => ?_
    simp only [Function.comp, qmul_val, qlift_val, castEntX_act]
    rfl
  have hinv : Q.val δ (qvar F .traceCur (castSlotX (F := F) S).inv (some (castSlotX (F := F) S).invIm))
      eK eF = invQX δ eK S := by
    rw [qvar_val]; rfl
  have hlift : Q.val δ (qlift F (CoeffExpr.sumList (castSlotX (F := F) S).ents EntX.act)) eK eF =
      algebraMap F 𝕂′ ((S.ents.map fun x => evalQX x.act eF).sum) := by
    rw [qlift_val]; simp only [castSlotX]; rw [castEntX_sumAct]
  unfold slotGateQX
  rw [qsub_val, qmul_val, qadd_val, qadd_val, hinv, hents, hlift]
  simp only [castSlotX]
  unfold pairFX pairDaX pairDbX
  cases hp : S.pair with
  | none => simp [qconst_val]
  | some q =>
    obtain ⟨fl, a, c, bl⟩ := q
    simp only [qmul_val, qadd_val, qlift_val, cc, CoeffExpr.eval, DX]

end Val

/-! ## 3. Row facts at a one-hot row -/

section Row
variable {F : Type} [Field F] {env : Env F} {j : ℕ}

theorem bool_of' {x : F} (h : x * (x - 1) = 0) : x = 0 ∨ x = 1 := by
  rcases mul_eq_zero.mp h with h | h
  · exact Or.inl h
  · exact Or.inr (sub_eq_zero.mp h)

theorem colBool (hB : BaseHoldsX env) {i : ℕ} (hi : (boolG (cc i) : CoeffExpr ℚ) ∈ oneHotG) :
    env.trace i = 0 ∨ env.trace i = 1 := by
  have a := arith_of_base hB (RowSemChipX.oneHotG_sub _ hi)
  simp only [boolG, cc, evalQX, Rat.cast_one] at a
  exact bool_of' a

theorem kc_bool (hB : BaseHoldsX env) {h : Hd} (hh : h ∈ allHandlesX) :
    evalQX (kcE h : CoeffExpr ℚ) env = 0 ∨ evalQX (kcE h : CoeffExpr ℚ) env = 1 := by
  have : evalQX (kcE h : CoeffExpr ℚ) env = kcV env h := by
    simp [kcE, kbE, cc, evalQX, kcV]
  rw [this]
  rcases kind_split hB h hh with ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ <;> simp [h1]

theorem kb_bool (hB : BaseHoldsX env) {h : Hd} (hh : h ∈ allHandlesX) :
    env.trace (kbX h) = 0 ∨ env.trace (kbX h) = 1 := by
  rcases kind_split hB h hh with ⟨-, h1⟩ | ⟨-, h1⟩ | ⟨-, h1⟩ <;> simp only [kbV] at h1 <;> simp [h1]

/-- The slot entries' state lists are in range and duplicate-free. -/
theorem slotsX_states_ok :
    ∀ S ∈ (ChipHX.slotsX : List (SlotX ℚ)), ∀ x ∈ S.ents, (∀ i ∈ x.states, i < nStates) ∧ x.states.Nodup := by
  decide

/-- Within a slot, entries have disjoint state lists. -/
theorem slotsX_states_disj :
    ∀ S ∈ (ChipHX.slotsX : List (SlotX ℚ)), (S.ents.map (·.states)).Pairwise fun a c => ∀ i ∈ a, i ∉ c := by
  decide

/-- The pair states are disjoint from every entry's states. -/
theorem slotsX_pair_disj :
    ∀ S ∈ (ChipHX.slotsX : List (SlotX ℚ)), ∀ x ∈ S.ents, ∀ i ∈ x.states, i ∉ S.pairStates := by
  decide

theorem extra_bool (hB : BaseHoldsX env) :
    ∀ S ∈ (ChipHX.slotsX : List (SlotX ℚ)), ∀ x ∈ S.ents, evalQX x.extra env = 0 ∨ evalQX x.extra env = 1 := by
  have hz := colBool hB (i := z1X) (by simp [oneHotG])
  have hf := colBool hB (i := fastX) (by simp [oneHotG])
  have hk := kc_bool hB (h := xSf1) (by decide)
  have n1 : ∀ i, (env.trace i = 0 ∨ env.trace i = 1) →
      evalQX (notC i : CoeffExpr ℚ) env = 0 ∨ evalQX (notC i : CoeffExpr ℚ) env = 1 := by
    intro i hi
    simp only [notC, cc, evalQX, Rat.cast_one]
    rcases hi with h | h <;> simp [h]
  intro S hS x hx
  simp only [ChipHX.slotsX, List.mem_cons, List.not_mem_nil, or_false] at hS
  rcases hS with rfl | rfl | rfl | rfl <;>
    simp only [slot0X, slot1X, slot2X, slot3X, List.mem_cons, List.not_mem_nil, or_false] at hx <;>
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;>
    first
    | exact n1 _ hz
    | exact n1 _ hf
    | exact hk
    | (right; simp [evalQX])

theorem ohZ (hOH : OneHotAt env j) {i : ℕ} (hi : i < nStates) (hne : i ≠ j) : env.trace i = 0 := by
  simpa [hne] using hOH i hi

theorem ohO (hOH : OneHotAt env j) (hj : j < nStates) : env.trace j = 1 := by
  simpa using hOH j hj

variable (hB : BaseHoldsX env) (hOH : OneHotAt env j)
include hB hOH

theorem act_val {S : SlotX ℚ} (hS : S ∈ (ChipHX.slotsX : List (SlotX ℚ))) {x : EntX ℚ} (hx : x ∈ S.ents) :
    evalQX x.act env = (if j ∈ x.states then 1 else 0) * evalQX x.extra env := by
  have hok := slotsX_states_ok S hS x hx
  simp only [EntX.act, evalQX, selS_onehot hOH x.states hok.1 hok.2]

theorem act_bool {S : SlotX ℚ} (hS : S ∈ (ChipHX.slotsX : List (SlotX ℚ))) :
    ∀ x ∈ S.ents, evalQX x.act env = 0 ∨ evalQX x.act env = 1 := by
  intro x hx
  rw [act_val hB hOH hS hx]
  split_ifs
  · rw [one_mul]; exact extra_bool hB S hS x hx
  · left; rw [zero_mul]

theorem act_zero {S : SlotX ℚ} (hS : S ∈ (ChipHX.slotsX : List (SlotX ℚ))) {x : EntX ℚ} (hx : x ∈ S.ents)
    (hj : j ∉ x.states) : evalQX x.act env = 0 := by
  rw [act_val hB hOH hS hx, if_neg hj, zero_mul]

theorem act_pairwise {S : SlotX ℚ} (hS : S ∈ (ChipHX.slotsX : List (SlotX ℚ))) :
    S.ents.Pairwise fun x y => evalQX x.act env * evalQX y.act env = 0 := by
  have hd := List.pairwise_map.mp (slotsX_states_disj S hS)
  refine List.Pairwise.imp_of_mem ?_ hd
  intro x y hx hy hxy
  by_cases hj : j ∈ x.states
  · rw [act_zero hB hOH hS hy (hxy j hj), mul_zero]
  · rw [act_zero hB hOH hS hx hj, zero_mul]

theorem prX_zero (h5 : j ≠ 5) (h12 : j ≠ 12) : env.trace prX = 0 := by
  have a := arith_of_base hB (op5G_sub _ (by simp [op5G] : (prGateX : CoeffExpr ℚ) ∈ op5G))
  have e5 : env.trace 5 = 0 := ohZ hOH (by decide) (Ne.symm h5)
  have e12 : env.trace sS10L = 0 := ohZ hOH (by decide) (Ne.symm h12)
  simp only [prGateX, prodL, List.foldr, cc, notC, evalQX, Rat.cast_one, e5, e12] at a
  linear_combination a

theorem prX_bool : env.trace prX = 0 ∨ env.trace prX = 1 := by
  by_cases h5 : j = 5
  · subst h5
    have a := arith_of_base hB (op5G_sub _ (by simp [op5G] : (prGateX : CoeffExpr ℚ) ∈ op5G))
    have e5 : env.trace 5 = 1 := ohO hOH (by decide)
    have e12 : env.trace sS10L = 0 := ohZ hOH (by decide) (by decide)
    have hβ := colBool hB (i := betaX) (by simp [oneHotG])
    have hz := colBool hB (i := z1X) (by simp [oneHotG])
    simp only [prGateX, prodL, List.foldr, cc, notC, evalQX, Rat.cast_one, e5, e12] at a
    have : env.trace prX = env.trace betaX * (1 - env.trace z1X) := by linear_combination a
    rw [this]
    rcases hβ with h | h <;> rcases hz with h' | h' <;> simp [h, h']
  · by_cases h12 : j = 12
    · subst h12
      have a := arith_of_base hB (op5G_sub _ (by simp [op5G] : (prGateX : CoeffExpr ℚ) ∈ op5G))
      have e5 : env.trace 5 = 0 := ohZ hOH (by decide) (by decide)
      have e12 : env.trace sS10L = 1 := ohO hOH (by decide)
      simp only [prGateX, prodL, List.foldr, cc, notC, evalQX, Rat.cast_one, e5, e12] at a
      right; linear_combination a
    · left; exact prX_zero hB hOH h5 h12

theorem pr2X_zero (h5 : j ≠ 5) : env.trace pr2X = 0 := by
  have a := arith_of_base hB (op5G_sub _ (by simp [op5G] : (pr2GateX : CoeffExpr ℚ) ∈ op5G))
  have e5 : env.trace 5 = 0 := ohZ hOH (by decide) (Ne.symm h5)
  simp only [pr2GateX, prodL, List.foldr, cc, kbE, evalQX, Rat.cast_one, e5] at a
  linear_combination a

theorem pr2X_bool : env.trace pr2X = 0 ∨ env.trace pr2X = 1 := by
  have a := arith_of_base hB (op5G_sub _ (by simp [op5G] : (pr2GateX : CoeffExpr ℚ) ∈ op5G))
  have hβ := colBool hB (i := betaX) (by simp [oneHotG])
  have h5 := colBool hB (i := 5)
    (List.mem_append_left _ (List.mem_map.mpr ⟨5, List.mem_range.mpr (by decide), rfl⟩))
  have k1 := kb_bool hB (h := xFtth) (by decide)
  have k2 := kb_bool hB (h := xFttt) (by decide)
  simp only [pr2GateX, prodL, List.foldr, cc, kbE, evalQX, Rat.cast_one] at a
  have : env.trace pr2X = env.trace 5 * (env.trace betaX * (env.trace (kbX xFtth) *
      (env.trace (kbX xFttt) * 1))) := by linear_combination a
  rw [this]
  rcases hβ with h | h <;> rcases h5 with h' | h' <;> rcases k1 with k | k <;> rcases k2 with k' | k' <;>
    simp [h, h', k, k']

/-- The pair flag is boolean. -/
theorem pairF_bool {S : SlotX ℚ} (hS : S ∈ (ChipHX.slotsX : List (SlotX ℚ))) :
    pairFX env S = 0 ∨ pairFX env S = 1 := by
  simp only [ChipHX.slotsX, List.mem_cons, List.not_mem_nil, or_false] at hS
  rcases hS with rfl | rfl | rfl | rfl
  · left; rfl
  · left; rfl
  · exact prX_bool hB hOH
  · exact pr2X_bool hB hOH

/-- The pair flag excludes the slot's entries. -/
theorem pairF_act {S : SlotX ℚ} (hS : S ∈ (ChipHX.slotsX : List (SlotX ℚ))) :
    ∀ x ∈ S.ents, pairFX env S * evalQX x.act env = 0 := by
  intro x hx
  by_cases hj : j ∈ x.states
  · have hnp := slotsX_pair_disj S hS x hx j hj
    have hS' := hS
    simp only [ChipHX.slotsX, List.mem_cons, List.not_mem_nil, or_false] at hS'
    rcases hS' with rfl | rfl | rfl | rfl
    · simp [pairFX, slot0X]
    · simp [pairFX, slot1X]
    · have h5 : j ≠ 5 := fun h => hnp (by simp [slot2X, h])
      have h12 : j ≠ 12 := fun h => hnp (by simp [slot2X, h])
      simp only [pairFX, slot2X]; rw [prX_zero hB hOH h5 h12, zero_mul]
    · have h5 : j ≠ 5 := fun h => hnp (by simp [slot3X, h])
      simp only [pairFX, slot3X]; rw [pr2X_zero hB hOH h5, zero_mul]
  · rw [act_zero hB hOH hS hx hj, mul_zero]

end Row

/-! ## 4. The row term of a balance -/

section Term
variable {F K : Type} [Field F] [Field K] [Algebra F K] [DecidableEq F] (δ : F)
  [Fact (¬ IsSquare (algebraMap F K δ))] (b : Basis (Fin 3) F K)

local notation "𝕂′" => Quad (algebraMap F K δ)

/-- The pair records of a slot consumed into balance `bl`. -/
def pairRecsB (eF : Env F) (bl : Bal) (S : SlotX ℚ) : List (List RE) :=
  match S.pair with
  | some (fl, a, c, b') => if b' = bl ∧ eF.trace fl = 1 then [a, c] else []
  | none => []

/-- **The records a row consumes into balance `bl`.** -/
def consQX (eF : Env F) (bl : Bal) : List (List RE) :=
  (ChipHX.slotsX (F := ℚ)).flatMap fun S =>
    (((S.ents.filter fun x => decide (x.bal = bl)).filter fun x => decide (evalQX x.act eF = 1)).map
      (·.rcd)) ++ pairRecsB eF bl S

/-- The `𝕂′` term of a row into balance `bl`: `Σ_S actB · inv′`. -/
def termQX (eF : Env F) (bl : Bal) : 𝕂′ :=
  ((ChipHX.slotsX : List (SlotX ℚ)).map fun S =>
    algebraMap F 𝕂′ (evalQX (S.actB bl) eF) * invQX δ (gatherEnv b eF) S).sum

theorem evalQX_actB (S : SlotX ℚ) (bl : Bal) (eF : Env F) :
    evalQX (S.actB bl) eF = ((S.ents.filter fun x => decide (x.bal = bl)).map fun x => evalQX x.act eF).sum +
      (match S.pair with
       | some (_, _, _, b') => if b' = bl then pairFX eF S else 0
       | none => 0) := by
  unfold SlotX.actB
  rw [evalQX, evalQX_sumList]
  congr 1
  unfold pairFX
  cases hp : S.pair with
  | none => simp [evalQX]
  | some q =>
    obtain ⟨fl, a, c, b'⟩ := q
    simp only
    split_ifs <;> simp [evalQX, cc]

/-- **A row's balance term is the reciprocal sum of its consumed records.** -/
theorem termQX_row {eF : Env F} {j : ℕ} (hB : BaseHoldsX eF) (hOH : OneHotAt eF j)
    (hg : ∀ S ∈ (ChipHX.slotsX : List (SlotX ℚ)), Q.val δ (slotGateQX F δ (castSlotX S)) (gatherEnv b eF) eF = 0)
    (hden : ∀ S ∈ (ChipHX.slotsX : List (SlotX ℚ)), pairFX eF S = 1 →
      pairDaX δ (gatherEnv b eF) eF S ≠ 0 ∧ pairDbX δ (gatherEnv b eF) eF S ≠ 0)
    (bl : Bal) :
    termQX δ b eF bl = ((consQX eF bl).map fun r => (DX δ (gatherEnv b eF) eF r)⁻¹).sum := by
  set eK := gatherEnv b eF
  rw [termQX, consQX, map_flatMap_sum]
  congr 1
  refine List.map_congr_left fun S hS => ?_
  have hcore := slot_core S.ents (fun x => evalQX x.act eF) (fun x => DX δ eK eF x.rcd)
    (fun x => decide (x.bal = bl)) (invQX δ eK S) (pairFX eF S) (pairDaX δ eK eF S) (pairDbX δ eK eF S)
    (act_bool hB hOH hS) (act_pairwise hB hOH hS) (pairF_bool hB hOH hS) (pairF_act hB hOH hS)
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

/-! ## 5. The accumulator telescope at the masks `17 / 18` -/

section Acc
variable {F K : Type} [Field F] [Field K] [Algebra F K] (bio : Basis (Fin 3) F K)
open Compute.LogUp (limbVal coord_limbVal limbVal_eq_of_coords Slot termCoord acc_telescope)

/-- The `𝕂` value of a row's accumulator term over `ℚ`-template slots. -/
def termValX (slots : List (Slot ℚ)) (env : Env F) : K :=
  (slots.map fun s => evalQX s.act env • limbVal bio env.trace s.invBase).sum

theorem evalQX_termCoord (slots : List (Slot ℚ)) (k : ℕ) (env : Env F) :
    evalQX (termCoord slots k) env =
      (slots.map fun s => evalQX s.act env * env.trace (s.invBase + k)).sum := by
  unfold termCoord; rw [evalQX_sumList]; rfl

theorem coord_termValX (slots : List (Slot ℚ)) (env : Env F) (k : Fin 3) :
    coord bio (termValX bio slots env) k = evalQX (termCoord slots k) env := by
  rw [evalQX_termCoord]
  induction slots with
  | nil => simp [termValX, coord]
  | cons s ss ih =>
      simp only [termValX, List.map_cons, List.sum_cons] at ih ⊢
      have hl := coord_limbVal bio env.trace s.invBase k
      simp only [coord] at ih hl ⊢
      rw [map_add, Finsupp.add_apply, map_smul, Finsupp.smul_apply, hl, ih, smul_eq_mul]

variable (slots : List (Slot ℚ)) (accBase pubBase : ℕ) (env : Env F)
  (h : ∀ g ∈ (accGatesX slots accBase pubBase : List (CoeffExpr ℚ)), evalQX g env = 0)
include h

theorem accInitX_zero (h17 : env.trace firstX = 1) : limbVal bio env.trace accBase = 0 := by
  apply limbVal_eq_of_coords bio 0 env.trace accBase
  intro k
  have hg := h (accInitX accBase k) (List.mem_append_left _ (List.mem_append_left _
    (List.mem_map.2 ⟨k, List.mem_range.2 k.isLt, rfl⟩)))
  simp only [accInitX, cc, evalQX, h17, one_mul] at hg
  rw [hg]; simp [coord]

theorem accStepX_eq (h18 : env.trace lastX = 0) :
    limbVal bio env.traceNext accBase = limbVal bio env.trace accBase + termValX bio slots env := by
  apply bio.repr.injective
  ext k
  have hg := h (accStepX slots accBase k) (List.mem_append_left _ (List.mem_append_right _
    (List.mem_map.2 ⟨k, List.mem_range.2 k.isLt, rfl⟩)))
  simp only [accStepX, notC, cc, evalQX, h18, sub_zero, Rat.cast_one, one_mul] at hg
  have h1 := coord_limbVal bio env.traceNext accBase k
  have h2 := coord_limbVal bio env.trace accBase k
  have h3 := coord_termValX bio slots env k
  simp only [coord] at h1 h2 h3
  simp only [map_add, Finsupp.coe_add, Pi.add_apply, h1, h2, h3]
  linear_combination hg

theorem accTermX_eq (h18 : env.trace lastX = 1) :
    limbVal bio env.trace accBase + termValX bio slots env = limbVal bio env.pub pubBase := by
  apply bio.repr.injective
  ext k
  have hg := h (accTermX slots accBase pubBase k) (List.mem_append_right _
    (List.mem_map.2 ⟨k, List.mem_range.2 k.isLt, rfl⟩))
  simp only [accTermX, cc, evalQX, h18, one_mul] at hg
  have h1 := coord_limbVal bio env.pub pubBase k
  have h2 := coord_limbVal bio env.trace accBase k
  have h3 := coord_termValX bio slots env k
  simp only [coord] at h1 h2 h3
  simp only [map_add, Finsupp.coe_add, Pi.add_apply, h1, h2, h3]
  linear_combination hg

omit h in
/-- **The accumulator over `N` rows** (masks `17 / 18`). -/
theorem accX_rows (N : ℕ) (hN : 0 < N) (envs : ℕ → Env F)
    (hg : ∀ i < N, ∀ g ∈ (accGatesX slots accBase pubBase : List (CoeffExpr ℚ)), evalQX g (envs i) = 0)
    (hshift : ∀ i, i + 1 < N → (envs i).traceNext = (envs (i + 1)).trace)
    (hfirst : (envs 0).trace firstX = 1)
    (hnotLast : ∀ i, i + 1 < N → (envs i).trace lastX = 0) (hlast : (envs (N - 1)).trace lastX = 1) :
    ∑ i ∈ Finset.range N, termValX bio slots (envs i) = limbVal bio (envs (N - 1)).pub pubBase := by
  refine acc_telescope N hN (fun i => limbVal bio (envs i).trace accBase)
    (fun i => termValX bio slots (envs i)) _ ?_ ?_ ?_
  · exact accInitX_zero bio slots accBase pubBase (envs 0) (hg 0 hN) hfirst
  · intro i hi
    have h' := accStepX_eq bio slots accBase pubBase (envs i) (hg i (by omega)) (hnotLast i hi)
    rw [hshift i hi] at h'
    exact h'
  · exact accTermX_eq bio slots accBase pubBase (envs (N - 1)) (hg (N - 1) (by omega)) hlast

end Acc

/-! ## 6. The three handle-class balances, compute side -/

section Bal
variable {F K : Type} [Field F] [Field K] [Algebra F K] [DecidableEq F] (δ : F)
  [Fact (¬ IsSquare (algebraMap F K δ))] (b : Basis (Fin 3) F K)
open Compute.LogUp (limbVal Slot)

local notation "𝕂′" => Quad (algebraMap F K δ)

/-- The accumulator slots of balance `bl` (Re or Im inverses). -/
def slotsB (bl : Bal) (im : Bool) : List (Slot ℚ) :=
  (ChipHX.slotsX : List (SlotX ℚ)).map fun S => ⟨S.actB bl, if im then S.invIm else S.inv⟩

/-- The accumulator / public columns of each balance: `(acc Re, pub Re, acc Im, pub Im)`. -/
def balCols : Bal → ℕ × ℕ × ℕ × ℕ
  | .x => (accXX, pubRhoX, accXXi, pubRhoXIm)
  | .p => (accPX, pubRhoP, accPXi, pubRhoPIm)
  | .s => (accSX, pubRhoSX, accSXi, pubRhoSXi)

theorem accRe_sub (bl : Bal) :
    ∀ g ∈ (accGatesX (slotsB bl false) (balCols bl).1 (balCols bl).2.1 : List (CoeffExpr ℚ)),
      g ∈ (baseGatesHX : List (CoeffExpr ℚ)) := by
  intro g hg
  refine List.mem_append_left _ (List.mem_append_right _ ?_)
  cases bl <;> simp only [accGatesHX, List.mem_append] <;> simp_all [accOf, slotsB, balCols]

theorem accIm_sub (bl : Bal) :
    ∀ g ∈ (accGatesX (slotsB bl true) (balCols bl).2.2.1 (balCols bl).2.2.2 : List (CoeffExpr ℚ)),
      g ∈ (baseGatesHX : List (CoeffExpr ℚ)) := by
  intro g hg
  refine List.mem_append_left _ (List.mem_append_right _ ?_)
  cases bl <;> simp only [accGatesHX, List.mem_append] <;> simp_all [accOf, slotsB, balCols]

theorem mk_list_sumX {ι : Type} (l : List ι) (f g : ι → K) :
    Quad.mk (algebraMap F K δ) (l.map f).sum (l.map g).sum =
      (l.map fun i => Quad.mk (algebraMap F K δ) (f i) (g i)).sum := by
  induction l with
  | nil => simp [Quad.mk_zero']
  | cons a t ih => simp only [List.map_cons, List.sum_cons]; rw [← ih, Quad.mk_add]

theorem mk_fsumX {ι : Type} (s : Finset ι) (f g : ι → K) :
    ∑ i ∈ s, Quad.mk (algebraMap F K δ) (f i) (g i) = Quad.mk (algebraMap F K δ) (∑ i ∈ s, f i) (∑ i ∈ s, g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Quad.mk_zero']
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, Finset.sum_insert ha, ih, Quad.mk_add]

/-- A row's `𝕂′` balance term is the pair (Re accumulator term, Im accumulator term). -/
theorem termQX_eq (eF : Env F) (bl : Bal) :
    termQX δ b eF bl = Quad.mk _ (termValX b (slotsB bl false) eF) (termValX b (slotsB bl true) eF) := by
  simp only [termValX, slotsB, List.map_map, Function.comp_def, Bool.false_eq_true, if_false, if_true]
  rw [mk_list_sumX, termQX]
  congr 1
  refine List.map_congr_left fun S _ => ?_
  rw [invQX, aMFX, Quad.mk_smul, Algebra.smul_def, Algebra.smul_def]
  rfl

end Bal

/-! ## 7. The accepted chip -/

section Chip
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq F]
  {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F) (b : Basis (Fin 3) F K) (δ : F)
  [Fact (¬ IsSquare (algebraMap F K δ))]
  (chalV pubVal : ℕ → F) (orbit : StrictOrbitDomain F 3 h)
  (P : Fin (computeChipVCLHX hn nodes b δ chalV pubVal orbit).rap.w → F[X])
open Compute.LogUp (limbVal)

local notation "𝕂′" => Quad (algebraMap F K δ)
local notation "EN" => envsN hn nodes chalV pubVal orbit P

/-- The slot pairs vanish at every row of an accepted trace. -/
theorem slotX_of_sat (hsat : RAP.SatisfiesWithPreprocessing (computeChipVCLHX hn nodes b δ chalV pubVal orbit) P)
    (x : F) (hx : x ∈ rowNodeSet nodes) (S : SlotX ℚ) (hS : S ∈ (ChipHX.slotsX : List (SlotX ℚ))) :
    Q.val δ (slotGateQX F δ (castSlotX S)) (gatherEnv b (Reify.envOfTrace P orbit.ω x chalV pubVal))
      (Reify.envOfTrace P orbit.ω x chalV pubVal) = 0 := by
  have hall := ((computeChipVCLHX_sat_iff hn nodes b δ chalV pubVal orbit P).mp hsat).2 x hx
  have hS' : castSlotX S ∈ (ChipHX.slotsX : List (SlotX F)) := by
    rw [← slotsX_cast]; exact List.mem_map_of_mem hS
  have hz : Q.IsZero (slotGateQX F δ (castSlotX S)) (gatherEnv b (Reify.envOfTrace P orbit.ω x chalV pubVal))
      (Reify.envOfTrace P orbit.ω x chalV pubVal) :=
    (Compute.TowerD.qGates_iff b (isCoordEnv_gather b _) _).mp fun g hg =>
      hall g (List.mem_append_left _ (List.mem_append_right _ (List.mem_flatMap.mpr
        ⟨_, List.mem_map_of_mem hS', hg⟩)))
  exact (Q.isZero_iff δ _ _ _).mp hz

/-- **The extraction context** of the compute balances (any field of characteristic `> 17`). -/
structure BCtx : Prop where
  hc : nStates < ringChar F
  hsat : RAP.SatisfiesWithPreprocessing (computeChipVCLHX hn nodes b δ chalV pubVal orbit) P
  hinj : Function.Injective nodes
  hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω

variable {hn nodes b δ chalV pubVal orbit P}
  (C : BCtx hn nodes b δ chalV pubVal orbit P)
include C

theorem envsN_ltB (k : ℕ) (hk : k < n) :
    envsN hn nodes chalV pubVal orbit P k = rEF nodes chalV pubVal orbit P ⟨k, hk⟩ := by
  simp [envsN, hk]

theorem baseB {r : ℕ} (hr : r < n) : BaseHoldsX (EN r) := by
  rw [envsN_ltB C r hr]
  exact baseX_of_sat hn nodes b δ chalV pubVal orbit P C.hsat _ (mem_rowNodeSet nodes _)

theorem slotB {r : ℕ} (hr : r < n) (S : SlotX ℚ) (hS : S ∈ (ChipHX.slotsX : List (SlotX ℚ))) :
    Q.val δ (slotGateQX F δ (castSlotX S)) (gatherEnv b (EN r)) (EN r) = 0 := by
  rw [envsN_ltB C r hr]
  exact slotX_of_sat hn nodes b δ chalV pubVal orbit P C.hsat _ (mem_rowNodeSet nodes _) S hS

theorem masksB {r : ℕ} (hr : r < n) :
    (EN r).trace firstX = (if r = 0 then 1 else 0) ∧ (EN r).trace lastX = (if r = n - 1 then 1 else 0) := by
  have hb := ((computeChipVCLHX_sat_iff hn nodes b δ chalV pubVal orbit P).mp C.hsat).1
  rw [envsN_ltB C r hr]
  exact masksCX hn nodes b δ chalV pubVal orbit P hb C.hinj ⟨r, hr⟩

theorem shiftB {r : ℕ} (hr : r + 1 < n) : (EN r).traceNext = (EN (r + 1)).trace := by
  funext j
  rw [envsN_ltB C r (by omega), envsN_ltB C (r + 1) hr]
  exact traceNext_eq nodes orbit P _ _ C.hadj ⟨r, by omega⟩ hr j

theorem pubB (r : ℕ) : (EN r).pub = pubVal := by
  unfold envsN; split_ifs <;> rfl

theorem accB_rows (slots : List (Compute.LogUp.Slot ℚ)) (accBase pubBase : ℕ)
    (hsub : ∀ g ∈ (accGatesX slots accBase pubBase : List (CoeffExpr ℚ)), g ∈ (baseGatesHX : List (CoeffExpr ℚ))) :
    ∑ i ∈ Finset.range n, termValX b slots (EN i) = limbVal b pubVal pubBase := by
  rw [accX_rows b slots accBase pubBase n hn EN (fun i hi g hg => baseB C hi g (hsub g hg))
    (fun i hi => shiftB C hi) (by rw [(masksB C hn).1]; simp)
    (fun i hi => by rw [(masksB C (by omega)).2]; simp; omega)
    (by rw [(masksB C (by omega)).2]; simp), pubB C]

/-- **The compute side of the J-8 handle-class balances**: on an accepted `computeChipVCLHX` trace, for
each balance `bl ∈ {x, p, s}` (cell export, walk path, service), the reciprocal sum of the records
the rows consume into `bl` is the public `(Re ρ_bl, Im ρ_bl)` — given nonzero pair denominators. -/
theorem compute_balanceX
    (hden : ∀ r < n, ∀ S ∈ (ChipHX.slotsX : List (SlotX ℚ)), pairFX (EN r) S = 1 →
      pairDaX δ (gatherEnv b (EN r)) (EN r) S ≠ 0 ∧ pairDbX δ (gatherEnv b (EN r)) (EN r) S ≠ 0)
    (bl : Bal) :
    ∑ i ∈ Finset.range n, ((consQX (EN i) bl).map fun r => (DX δ (gatherEnv b (EN i)) (EN i) r)⁻¹).sum =
      Quad.mk (algebraMap F K δ) (limbVal b pubVal (balCols bl).2.1) (limbVal b pubVal (balCols bl).2.2.2) := by
  have hrow : ∀ i ∈ Finset.range n,
      ((consQX (EN i) bl).map fun r => (DX δ (gatherEnv b (EN i)) (EN i) r)⁻¹).sum =
        Quad.mk (algebraMap F K δ) (termValX b (slotsB bl false) (EN i)) (termValX b (slotsB bl true) (EN i)) := by
    intro i hi
    have hi' := Finset.mem_range.mp hi
    rw [← termQX_eq, termQX_row δ b (baseB C hi') (stX_spec (baseB C hi') C.hc)
      (fun S hS => slotB C hi' S hS) (hden i hi') bl]
  rw [Finset.sum_congr rfl hrow, mk_fsumX, accB_rows C _ _ _ (accRe_sub bl),
    accB_rows C _ _ _ (accIm_sub bl)]

end Chip

/-! ## 8. The consumed records are `RowSemChipX.activeX`'s, per balance -/

section Active
variable {p : ℕ} [Fact p.Prime]
open Nock.NockVMROM.Thm54.VclL.Handle.RowSemChipX (activeX pairRecsX reVal)

/-- **`consQX` is `activeX` filtered by balance** (records read as `ZMod.val` values): the records
summed by `compute_balanceX` are exactly those `RecOK` must hold of. -/
theorem consQX_activeX (env : Env (ZMod p)) (bl : Bal) :
    ((activeX env).filter fun r => decide (r.2 = bl)).map (·.1) =
      (consQX env bl).map (·.map (reVal env)) := by
  unfold activeX consQX
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

end

end Nock.NockVMROM.Thm54.VclL.Handle.TeleCQX
