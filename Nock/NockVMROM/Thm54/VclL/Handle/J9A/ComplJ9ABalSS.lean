/-
  Nock/NockVMROM/Thm54/VclL/Handle/J9A/ComplJ9ABalSS.lean

`spSum δ nA vS mS χ = Σ_{i : Fin n} rowT i` is regrouped by field axis value:
  * `rowT_eq`: split row `i` is `mS i • Σ_{limbRecs (nA + i) (vS i)} limbW` (`limbRecs_field`, `d2_eq`/`d3_eq`).
  * `spSum_gen`: with `vS i = fx[i]` (`fx = fieldAx9 p rows`) and `mS i` = #distinct keys with axis `vS i` + #`s10B` rows
    with `n = vS i`, `spSum` = Σ_{field keys} Σ_{limbRecs (idOf9 k.2) k.2} limbW + Σ_{field s10B rows} Σ_{limbRecs
    (idOf9 l.n) l.n} limbW.
  * `spSum_run`: at the J-9 A data (`nAA`, `vSA`, `mSA`), including the absent case.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.ComplJ9ABalSAx
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.ComplJ9ARun

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ABalSS

noncomputable section

open Nock Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.T0Tower Nock.NockVMROM.Thm54.StrictExtension
open Nock.NockVMROM.Thm54.SVFrame Nock.NockVMROM.Thm54.CoordinateCompiler Nock.NockVMROM.Thm54.VclL
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8 Nock.NockVMROM.Thm54.VclL.Handle.VerJ8
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Bad
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AGen
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AChains
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AChainsRun
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ABalSAx
open Nock.Walk Nock.Edit Nock.Edit.GenX
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ABinders Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AData

/-! ## 1. Generic list lemmas -/

theorem sum_fin_getD {M : Type} [AddCommMonoid M] (g : ℕ → M) :
    ∀ (fx : List ℕ), (∑ i : Fin fx.length, g (fx.getD i 0)) = (fx.map g).sum := by
  intro fx
  rw [Fin.sum_univ_eq_sum_range (fun i => g (fx.getD i 0)) fx.length]
  induction fx with
  | nil => simp
  | cons a l ih =>
    rw [List.length_cons, Finset.sum_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero, List.map_cons, List.sum_cons]
    rw [ih, add_comm]

theorem filterMap_map_eq {α β M : Type} (L : List α) (pr : α → Bool) (g : α → β) (f : α → Option β)
    (hf : ∀ x, f x = if pr x = true then some (g x) else none) (w : β → M) :
    (L.filterMap f).map w = (L.filter pr).map (fun x => w (g x)) := by
  induction L with
  | nil => simp
  | cons x L ih =>
    by_cases hx : pr x = true
    · simp [List.filterMap_cons, List.filter_cons, hf x, hx, ih]
    · simp [List.filterMap_cons, List.filter_cons, hf x, hx, ih]

/-! ## 2. One split row -/

section Row
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

/-- `Σ_{limbRecs R n} limbW`. -/
def limbSum (R n : ℕ) (χ : Coins frameJ8 K) : 𝕂′ := ((limbRecs (p := p) R n).map (limbW δ χ)).sum

theorem recDenP_zero (γ : 𝕂′) (a b c d : ZMod p) :
    recDenP 0 γ (a, b, (c, d)) = ComplJ9AChipsOK.xKey4 δ γ a b c d := by
  simp [recDenP, ComplJ9AChipsOK.xKey4, liftQ, IsScalarTower.algebraMap_apply (ZMod p) K 𝕂′]

/-- **One split row**: `rowT i = mS i • Σ_{limbRecs (nA + i) (vS i)} limbW`. -/
theorem rowT_eq (nA : ℕ) {n : ℕ} (vS mS : Fin n → ℕ) (χ : Coins frameJ8 K) (i : Fin n)
    (hv : 2 ^ 32 ≤ vS i ∧ vS i < 2 ^ 64) :
    Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ASplitH.rowT δ (chalsMJ8 δ χ) nA vS mS i =
      mS i • limbSum δ (nA + (i : ℕ)) (vS i) χ := by
  unfold Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ASplitH.rowT
  rw [ComplJ9AChipsOK.d2_eq, ComplJ9AChipsOK.d3_eq, ComplJ9ABalSAx.liftQ_nat]
  unfold limbSum
  rw [limbRecs_field _ _ hv.1 hv.2]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, limbW,
    recDenP_zero δ, ComplJ9AChipsOK.x2, ComplJ9AChipsOK.x3]
  rw [add_comm]

end Row

/-! ## 3. Regrouping by value -/

section Gen
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

/-- **The split side, generic**: `vS i = fx[i]` (`fx = fieldAx9 p rows`), `mS i` = #distinct keys with axis `vS i`
+ #`s10B` rows with `n = vS i`.  Then `spSum` is the limb consumes of the field keys plus those of the field
`s10B` rows. -/
theorem spSum_gen (nA : ℕ) (H : Noun → ℕ × ℕ) (rows : Array LX9)
    (fx : List ℕ) (hfx : fx = fieldAx9 p rows)
    (hv : ∀ v ∈ fx, 2 ^ 32 ≤ v ∧ v < 2 ^ 64) {n : ℕ} (hn : n = fx.length)
    (vS mS : Fin n → ℕ) (hvS : ∀ i, vS i = fx.getD i 0)
    (hmS : ∀ i, mS i = ((axKeys9 rows).filter (·.2 = vS i)).length +
      (rows.toList.filter fun l => l.chip = .s10B ∧ l.n = vS i).length) (χ : Coins frameJ8 K) :
    ComplJ9AChipsOK.spSum δ nA vS mS χ =
      (((axKeys9 rows).filter fun k => decide (k.2 < p)).map fun k =>
        limbSum δ (idOf9 p nA H fx k.2) k.2 χ).sum +
      ((rows.toList.filter fun l => decide (l.chip = .s10B ∧ l.n < p)).map fun l =>
        limbSum δ (idOf9 p nA H fx l.n) l.n χ).sum := by
  subst hn
  have hnd : fx.Nodup := hfx ▸ fieldAx9_nodup p rows
  have hmemlt : ∀ v ∈ fx, v < p := fun v hv' => by
    simp only [hfx, fieldAx9, List.mem_filter, decide_eq_true_eq] at hv'; exact hv'.2
  let w : ℕ → 𝕂′ := fun v => limbSum δ (idOf9 p nA H fx v) v χ
  let c1 : ℕ → ℕ := fun v => ((axKeys9 rows).filter (·.2 = v)).length
  let c2 : ℕ → ℕ := fun v => (rows.toList.filter fun l => l.chip = .s10B ∧ l.n = v).length
  -- step 1: each row
  have hrow : ∀ i : Fin fx.length,
      Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ASplitH.rowT δ (chalsMJ8 δ χ) nA vS mS i =
        (c1 (fx.getD i 0) + c2 (fx.getD i 0)) • w (fx.getD i 0) := by
    intro i
    have hmem : fx.getD i 0 ∈ fx := by
      rw [List.getD_eq_getElem _ _ i.2]; exact List.getElem_mem _
    rw [rowT_eq δ nA vS mS χ i (by rw [hvS]; exact hv _ hmem), hmS i, hvS i]
    have hid : idOf9 p nA H fx (fx.getD i 0) = nA + (i : ℕ) := by
      rw [idOf9_field (hmemlt _ hmem), List.getD_eq_getElem _ _ i.2, hnd.idxOf_getElem i.1 i.2]
    simp only [w, hid, c1, c2]
  unfold ComplJ9AChipsOK.spSum
  rw [Finset.sum_congr rfl fun i _ => hrow i]
  rw [sum_fin_getD (fun v => (c1 v + c2 v) • w v) fx]
  simp only [add_smul, List.sum_map_add]
  congr 1
  · -- keys
    have := sum_count_smul (β := Noun × ℕ) (M := 𝕂′)
      (fun k => if k.2 < p then some k.2 else none) fx hnd w (axKeys9 rows) (by
        intro l hl k hk
        by_cases hlt : l.2 < p
        · simp only [hlt, if_true, Option.some.injEq] at hk
          subst hk
          obtain ⟨l', hl', hl'k⟩ := mem_axKeys9.1 hl
          have : l.2 ∈ axAtoms9 rows := by
            refine mem_axAtoms9.2 ⟨l', hl', ?_, ?_⟩ <;> unfold axKey9 at hl'k <;>
              cases hc : l'.chip <;> simp [hc] at hl'k <;> subst hl'k <;> simp [hc]
          simp only [hfx, fieldAx9, List.mem_filter, decide_eq_true_eq]
          exact ⟨this, hlt⟩
        · simp [hlt] at hk)
    rw [filterMap_map_eq (axKeys9 rows) (fun k => decide (k.2 < p)) (fun k => k.2)
      (fun k => if k.2 < p then some k.2 else none) (fun k => by simp) w] at this
    rw [← this]
    refine congrArg List.sum (List.map_congr_left fun v hv' => ?_)
    have hvl := hmemlt v hv'
    congr 1
    refine congrArg List.length (List.filter_congr fun k _ => ?_)
    by_cases h : k.2 = v
    · simp [h, hvl]
    · simp [h]
  · -- s10B rows
    have := sum_count_smul (β := LX9) (M := 𝕂′)
      (fun l => if l.chip = .s10B ∧ l.n < p then some l.n else none) fx hnd w rows.toList (by
        intro l hl k hk
        by_cases hlt : l.chip = .s10B ∧ l.n < p
        · simp only [hlt, and_self, if_true, Option.some.injEq] at hk
          subst hk
          have : l.n ∈ axAtoms9 rows := mem_axAtoms9.2 ⟨l, hl, Or.inr hlt.1, rfl⟩
          simp only [hfx, fieldAx9, List.mem_filter, decide_eq_true_eq]
          exact ⟨this, hlt.2⟩
        · simp [hlt] at hk)
    rw [filterMap_map_eq rows.toList (fun l => decide (l.chip = .s10B ∧ l.n < p)) (fun l => l.n)
      (fun l => if l.chip = .s10B ∧ l.n < p then some l.n else none) (fun l => by simp) w] at this
    rw [← this]
    refine congrArg List.sum (List.map_congr_left fun v hv' => ?_)
    have hvl := hmemlt v hv'
    congr 1
    refine congrArg List.length (List.filter_congr fun l _ => ?_)
    by_cases h : l.chip = .s10B ∧ l.n = v
    · simp [h, hvl]
    · by_cases h2 : l.chip = .s10B <;> by_cases h3 : l.n = v <;> simp_all

end Gen

/-! ## 4. At the J-9 A data -/

section Run
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ARun (nAA vSA mSA spOnA nSOf nSOf_eq nSOf_pos)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ADataRec (j9aDataOf)
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  {Rg : Nock.Jet.VerifiedRegistry} (Rt : ℕ → Nock.Jet.Autogen.Tpl) {fuel : ℕ} {s f r : Noun}
  {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r))

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

/-- **C3 split side (S7)**: at the J-9 A data, the split chip's honest terminal `spSum` is the limb consumes of the
field-axis chains (one per distinct field key) plus those of the field-axis `s10B` rows.  Binders: `hpG`, `hax9`
only.  Absent case (`spOnA = false`): both sides are `0`. -/
theorem spSum_run (hpG : p = Nock.Atoms.p) (hax9 : ProgAxOK9A p t) (χ : Coins frameJ8 K) :
    ComplJ9AChipsOK.spSum δ (nAA (p := p) Rt hgen) (vSA (p := p) (t := t)) (mSA (p := p) (t := t)) χ =
      ((((axKeys9 (rowsOfT9 t)).filter fun k => decide (k.2 < p)).map fun k =>
        limbSum δ (idOf9 p (j9aDataOf p Rg Rt hgen).acs.length (j9aDataOf p Rg Rt hgen).H
          (fieldAx9 p (rowsOfT9 t)) k.2) k.2 χ).sum) +
      ((((rowsOfT9 t).toList.filter fun l => decide (l.chip = .s10B ∧ l.n < p)).map fun l =>
        limbSum δ (idOf9 p (j9aDataOf p Rg Rt hgen).acs.length (j9aDataOf p Rg Rt hgen).H
          (fieldAx9 p (rowsOfT9 t)) l.n) l.n χ).sum) := by
  by_cases hsp : spOnA p t = true
  · exact spSum_gen δ _ _ (rowsOfT9 t) (splitVals9 p (rowsOfT9 t)) rfl
      (ComplJ9AChainsRun.splitVals9_range hgen hpG hax9) (nSOf_eq hsp) _ _ (fun i => rfl) (fun i => rfl) χ
  · -- absent: no field axis atom
    have hfx : fieldAx9 p (rowsOfT9 t) = [] := by
      simpa [spOnA, ComplJ9AChainsRun.splitVals9] using hsp
    have hcap := axAtoms9_cap hgen hax9
    have hK0 : ∀ k ∈ axKeys9 (rowsOfT9 t), k.2 ≠ 0 := fun k hk => by
      have := (axKeys9_read hgen hk).1; positivity
    have hkeys : ((axKeys9 (rowsOfT9 t)).filter fun k => decide (k.2 < p)) = [] := by
      refine List.filter_eq_nil_iff.2 fun k hk => ?_
      obtain ⟨l', hl', hl'k⟩ := mem_axKeys9.1 hk
      have hat : k.2 ∈ axAtoms9 (rowsOfT9 t) := by
        refine mem_axAtoms9.2 ⟨l', hl', ?_, ?_⟩ <;> unfold axKey9 at hl'k <;>
          cases hc : l'.chip <;> simp [hc] at hl'k <;> subst hl'k <;> simp [hc]
      have : k.2 ∉ fieldAx9 p (rowsOfT9 t) := by rw [hfx]; simp
      simp only [fieldAx9, List.mem_filter, decide_eq_true_eq, not_and] at this
      simpa using this hat
    have hrows : ((rowsOfT9 t).toList.filter fun l => decide (l.chip = .s10B ∧ l.n < p)) = [] := by
      refine List.filter_eq_nil_iff.2 fun l hl hd => ?_
      simp only [decide_eq_true_eq] at hd
      have hat : l.n ∈ axAtoms9 (rowsOfT9 t) := mem_axAtoms9.2 ⟨l, hl, Or.inr hd.1, rfl⟩
      have : l.n ∈ fieldAx9 p (rowsOfT9 t) := by
        simp only [fieldAx9, List.mem_filter, decide_eq_true_eq]; exact ⟨hat, hd.2⟩
      rw [hfx] at this; simp at this
    rw [hkeys, hrows]
    simp only [List.map_nil, List.sum_nil, add_zero]
    unfold ComplJ9AChipsOK.spSum
    refine Finset.sum_eq_zero fun i _ => ?_
    have hm : mSA (p := p) (t := t) i = 0 := by
      have hv0 : vSA (p := p) (t := t) i = 0 := by
        simp [ComplJ9ARun.vSA, ComplJ9AChainsRun.splitVals9, hfx]
      unfold ComplJ9ARun.mSA
      rw [hv0]
      have h1 : (axKeys9 (rowsOfT9 t)).filter (fun x => decide (x.2 = 0)) = [] :=
        List.filter_eq_nil_iff.2 fun k hk hd => hK0 k hk (by simpa using hd)
      have h2 : (rowsOfT9 t).toList.filter (fun l => decide (l.chip = .s10B ∧ l.n = 0)) = [] := by
        refine List.filter_eq_nil_iff.2 fun l hl hd => ?_
        simp only [decide_eq_true_eq] at hd
        have hat : l.n ∈ axAtoms9 (rowsOfT9 t) := mem_axAtoms9.2 ⟨l, hl, Or.inr hd.1, rfl⟩
        have := (hcap _ hat).1
        rw [hd.2] at this; omega
      rw [h1, h2]; rfl
    unfold Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ASplitH.rowT
    rw [hm]; simp

end Run

section Axioms
#print axioms sum_fin_getD
#print axioms filterMap_map_eq
#print axioms recDenP_zero
#print axioms rowT_eq
#print axioms spSum_gen
#print axioms spSum_run
end Axioms

end

end Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ABalSS
