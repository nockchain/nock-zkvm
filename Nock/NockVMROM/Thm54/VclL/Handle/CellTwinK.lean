/-
  Nock/NockVMROM/Thm54/VclL/Handle/CellTwinK.lean

  * F1 (a) `cellRow_rank_pos`: a `RowOK` cell row has rank `lo + hi ≥ 1`.
  * F1 (b) `rank0_child_from_outside`: under the two-provider validity balance (cell rows + external
    providers `vp`), a weighted child whose key has rank `(0,0)` is provided by `vp`, never by a
    cell row (`no_cell_provides_rank0`).  Stated on the table-level `vProv/vCons`, the semantic
    counterparts of the chip's `vKeyP` (`(lo,hi)` entries) and `vKeyL/R`.
  * `cellChipHQK` = restriction twin of `cellChipHQ`: base columns `kbL kbR invL invR` = `130..133`,
    per side the gates `kb(1-kb)`, `kb·lo`, `kb·hi`, `w(1-kb)((lo+hi)inv-1)` and (see the DEVIATION
    in `kindGates`) `kb(1-w)`.  Width `242`.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.RangeHQ

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Nock.NockVMROM.Thm54.VclL.Handle.CellTwinK

open Nock Nock.Reified Nock.Framework
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.VclL.Handle Nock.NockVMROM.Thm54.VclL.Handle.RangeHQ
open Module
open scoped Polynomial

/-! ## 1. F1: rank positivity and the routing receipt -/

section F1
variable {q : ℕ} {Kfp : Type*} [Field Kfp] [Algebra (ZMod q) Kfp]

/-- **F1 (a)**: every accepted cell row has rank `lo + hi ≥ 1` (in fact `μ ≥ 1`). -/
theorem cellRow_rank_pos [Fact q.Prime] (hq : 2 ^ 63 < q) {z : Kfp} {c : CellRow q Kfp}
    (h : RowOK z c) : 1 ≤ c.b0.lo + c.b0.hi := by
  have := rowOK_mu hq h
  unfold CellRowB0.mu CellRowB0.muL CellRowB0.muR at this
  omega

/-- The two-provider validity balance: the cell rows AND external providers `vp` (weight 1 each)
provide; the cell rows' weighted children and the external lookups `vl` consume. -/
def ValidityBalanced2 (t : List (CellRow q Kfp)) (vp vl : List (VKey Kfp)) : Prop :=
  (expand (vProv t ++ vp.map (·, 1))).Perm (expand (vCons t ++ vl.map (·, 1)))

/-- No key provided by a cell row has rank `(0, 0)`. -/
theorem no_cell_provides_rank0 [Fact q.Prime] (hq : 2 ^ 63 < q) {z : Kfp} {t : List (CellRow q Kfp)}
    (hrows : ∀ c ∈ t, RowOK z c) {k : VKey Kfp} (hk : k ∈ expand (vProv t))
    (h0 : k.2.1 = 0 ∧ k.2.2.1 = 0) : False := by
  rw [mem_expand] at hk
  obtain ⟨kc, hkc, -, rfl⟩ := hk
  simp only [vProv, List.mem_map] at hkc
  obtain ⟨c, hc, rfl⟩ := hkc
  have := cellRow_rank_pos hq (hrows c hc)
  simp only at h0
  omega

/-- **F1 (b), routing receipt (left child)**: in a two-provider balanced table, a weighted left child
with rank `(0, 0)` is served by an EXTERNAL provider (`vp`), not by any cell row. -/
theorem rank0_child_from_outside_left [Fact q.Prime] (hq : 2 ^ 63 < q) {z : Kfp}
    {t : List (CellRow q Kfp)} {vp vl : List (VKey Kfp)} (hrows : ∀ c ∈ t, RowOK z c)
    (hbal : ValidityBalanced2 t vp vl) {c : CellRow q Kfp} (hc : c ∈ t) (hw : c.b0.wL = true)
    (h0 : c.b0.hiL = 0 ∧ c.b0.loL = 0) : (c.l, c.b0.hiL, c.b0.loL, c.b0.idL) ∈ vp := by
  have hmem : (c.l, c.b0.hiL, c.b0.loL, c.b0.idL) ∈ expand (vCons t ++ vl.map (·, 1)) := by
    rw [mem_expand]
    refine ⟨((c.l, c.b0.hiL, c.b0.loL, c.b0.idL), 1), ?_, one_ne_zero, rfl⟩
    apply List.mem_append_left
    simp only [vCons, List.mem_flatMap]
    exact ⟨c, hc, by simp [hw]⟩
  have hprov := hbal.mem_iff.mpr hmem
  rw [expand, List.flatMap_append, List.mem_append] at hprov
  rcases hprov with hp | hp
  · exact (no_cell_provides_rank0 hq hrows (k := (c.l, c.b0.hiL, c.b0.loL, c.b0.idL)) hp h0).elim
  · simpa [List.mem_flatMap, List.mem_replicate] using hp

/-- Right-child twin of `rank0_child_from_outside_left`. -/
theorem rank0_child_from_outside_right [Fact q.Prime] (hq : 2 ^ 63 < q) {z : Kfp}
    {t : List (CellRow q Kfp)} {vp vl : List (VKey Kfp)} (hrows : ∀ c ∈ t, RowOK z c)
    (hbal : ValidityBalanced2 t vp vl) {c : CellRow q Kfp} (hc : c ∈ t) (hw : c.b0.wR = true)
    (h0 : c.b0.hiR = 0 ∧ c.b0.loR = 0) : (c.r, c.b0.hiR, c.b0.loR, c.b0.idR) ∈ vp := by
  have hmem : (c.r, c.b0.hiR, c.b0.loR, c.b0.idR) ∈ expand (vCons t ++ vl.map (·, 1)) := by
    rw [mem_expand]
    refine ⟨((c.r, c.b0.hiR, c.b0.loR, c.b0.idR), 1), ?_, one_ne_zero, rfl⟩
    apply List.mem_append_left
    simp only [vCons, List.mem_flatMap]
    exact ⟨c, hc, by simp [hw]⟩
  have hprov := hbal.mem_iff.mpr hmem
  rw [expand, List.flatMap_append, List.mem_append] at hprov
  rcases hprov with hp | hp
  · exact (no_cell_provides_rank0 hq hrows (k := (c.r, c.b0.hiR, c.b0.loR, c.b0.idR)) hp h0).elim
  · simpa [List.mem_flatMap, List.mem_replicate] using hp

/-- **Cell-only honest side condition**: with NO external provider (`vp = []`), every weighted child
of a balanced table has rank `≥ 1` (so `(lo + hi)` is invertible in a field of characteristic
`> 2^63`). -/
theorem cellOnly_child_rank_pos_left [Fact q.Prime] (hq : 2 ^ 63 < q) {z : Kfp}
    {t : List (CellRow q Kfp)} {vl : List (VKey Kfp)} (hrows : ∀ c ∈ t, RowOK z c)
    (hbal : ValidityBalanced t vl) {c : CellRow q Kfp} (hc : c ∈ t) (hw : c.b0.wL = true) :
    1 ≤ c.b0.loL + c.b0.hiL := by
  obtain ⟨c', hc', -, h1, h2, -⟩ := consumed_left_of_balanced hbal hc hw
  have := cellRow_rank_pos hq (hrows c' hc')
  omega

theorem cellOnly_child_rank_pos_right [Fact q.Prime] (hq : 2 ^ 63 < q) {z : Kfp}
    {t : List (CellRow q Kfp)} {vl : List (VKey Kfp)} (hrows : ∀ c ∈ t, RowOK z c)
    (hbal : ValidityBalanced t vl) {c : CellRow q Kfp} (hc : c ∈ t) (hw : c.b0.wR = true) :
    1 ≤ c.b0.loR + c.b0.hiR := by
  obtain ⟨c', hc', -, h1, h2, -⟩ := consumed_right_of_balanced hbal hc hw
  have := cellRow_rank_pos hq (hrows c' hc')
  omega

end F1

/-! ## 2. The restriction twin -/

section Twin
variable {F : Type} [Field F]

/-- Added base columns (after `cellTemplateHQ`'s `130`): the kind bits and the rank inverses. -/
def kbL : ℕ := 130
def kbR : ℕ := 131
def invL : ℕ := 132
def invR : ℕ := 133

def sideGates (kb inv w lo hi : ℕ) : List (CoeffExpr F) :=
  [ boolE (cv kb), .mul (cv kb) (cv lo), .mul (cv kb) (cv hi),
    .mul (.mul (cv w) (notE (cv kb))) (.sub (.mul (.add (cv lo) (cv hi)) (cv inv)) (.const 1)),
    .mul (cv kb) (notE (cv w)) ]

def kindGates : List (CoeffExpr F) :=
  sideGates kbL invL Cell.wL Cell.loL Cell.hiL ++ sideGates kbR invR Cell.wR Cell.loR Cell.hiR

theorem sideGates_deg (kb inv w lo hi : ℕ) :
    ∀ g ∈ (sideGates (F := F) kb inv w lo hi), g.degree ≤ 4 := by
  intro g hg
  simp only [sideGates, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl <;> simp [CoeffExpr.degree]

theorem kindGates_deg : ∀ g ∈ (kindGates (F := F)), g.degree ≤ 4 := by
  intro g hg
  rcases List.mem_append.mp hg with h | h <;> exact sideGates_deg _ _ _ _ _ g h

theorem kindGates_below : ∀ g ∈ (kindGates (F := F)), colsBelow 134 g = true := by
  intro g hg
  simp only [kindGates, sideGates, List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
    at hg
  rcases hg with (rfl | rfl | rfl | rfl | rfl) | (rfl | rfl | rfl | rfl | rfl) <;>
    simp [colsBelow, kbL, kbR, invL, invR, Cell.wL, Cell.wR, Cell.loL, Cell.hiL, Cell.loR, Cell.hiR]

/-- **The kind-bit twin template**: `cellTemplateHQ` + 4 base columns + `kindGates`. -/
def cellTemplateHQK (δF : F) : ChipTemplate F where
  rounds := 3
  rounds_pos := by decide
  baseColsOf := ![134, 0, 0]
  extColsOf := ![0, 18, 18]
  baseTransition := Cell.baseGates ++ kindGates
  extTransition := []
  mixedTransition := Cell.mixedGates δF ++ CellHQ.gates δF
  extDeg1 := []
  extDeg3 := []
  equalityChecks := []
  baseTransition_deg := by
    intro g hg
    rcases List.mem_append.mp hg with h | h
    · exact cellBase_deg g h
    · exact kindGates_deg g h
  extTransition_deg := by simp
  mixedTransition_deg := CellHQ.mixed_deg δF
  extDeg1_deg := by simp
  extDeg3_deg := by simp
  equalityChecks_deg := by simp

theorem cellTemplateHQK_baseCols (δF : F) : (cellTemplateHQK δF).baseCols = 134 := by
  show (∑ r : Fin 3, (![134, 0, 0] : Fin 3 → ℕ) r) = 134
  decide
theorem cellTemplateHQK_extCols (δF : F) : (cellTemplateHQK δF).extCols = 36 := by
  show (∑ r : Fin 3, (![0, 18, 18] : Fin 3 → ℕ) r) = 36
  decide

end Twin

section Chip
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]

/-- **`cellChipHQK`**: the `𝕂′` cell twin with the kind bits (masks at `0`, `1`, as `cellChipHQ`). -/
noncomputable def cellChipHQK (δF : F) (b : Basis (Fin 3) F K) {h n : ℕ} (hn : 0 < n)
    (nodes : Fin n → F) (orbit : StrictOrbitDomain F 3 h) (chals pubs : ℕ → K) :
    FixedPreprocessingRAP F where
  rap := expandChip (cellTemplateHQK δF) b (slotVal b 134 chals) (slotVal b 134 pubs) orbit
    (rowNodeSet nodes)
  rounds_pos := by show 0 < 3; omega
  fixedCount := 2
  preprocessingIndex :=
    { toFun := fun j => ⟨j, by
        have := j.isLt
        show (j : ℕ) < 134 + 0 * 3
        omega⟩
      inj' := by intro i j hij; exact Fin.ext (by simpa using congrArg Fin.val hij) }
  preprocessing
    | 0 => firstRowMask nodes
    | 1 => lastRowMask hn nodes

variable (δF : F) (b : Basis (Fin 3) F K) {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F)
  (orbit : StrictOrbitDomain F 3 h) (chals pubs : ℕ → K)

/-- **Width `242`** (`134 + 36·3`), by `rfl`. -/
theorem cellChipHQK_width : (cellChipHQK δF b hn nodes orbit chals pubs).rap.w = 242 := rfl

theorem cellHQK_shift : ∀ j < (cellTemplateHQ δF).width 3,
    shiftCol 130 134 j < (cellTemplateHQK δF).width 3 :=
  shift_lt _ _ 130 134 (cellTemplateHQ_baseCols δF) (cellTemplateHQK_baseCols δF) (by omega)
    (by rw [cellTemplateHQ_extCols, cellTemplateHQK_extCols])

/-- Restriction of a twin trace to `cellChipHQ`'s `238` columns. -/
noncomputable def restrictCellQK
    (Q : Fin (cellChipHQK δF b hn nodes orbit chals pubs).rap.w → F[X]) :
    Fin (cellChipHQ δF b hn nodes orbit chals pubs).rap.w → F[X] :=
  restrictQ 130 134 (cellHQK_shift δF) Q

/-- **`restrict`**: twin-accepted ⇒ `cellChipHQ`-accepted on the restricted trace
(`expandChip_restrict`; the original's gates are the twin's, all reading columns `< 130`). -/
theorem cellChipHQK_restrict_sat
    (Q : Fin (cellChipHQK δF b hn nodes orbit chals pubs).rap.w → F[X])
    (hsat : (cellChipHQK δF b hn nodes orbit chals pubs).rap.Satisfies Q) :
    (cellChipHQ δF b hn nodes orbit chals pubs).rap.Satisfies
      (restrictCellQK δF b hn nodes orbit chals pubs Q) := by
  obtain ⟨hB, hM, -, -⟩ := cellHQ_range δF
  exact expandChip_restrict b orbit (rowNodeSet nodes) chals pubs (cellTemplateHQ δF)
    (cellTemplateHQK δF) 130 134 (cellTemplateHQ_baseCols δF) (cellTemplateHQK_baseCols δF)
    (by omega) (by rw [cellTemplateHQ_extCols, cellTemplateHQK_extCols])
    (fun g hg => ⟨List.mem_append_left _ hg, by
      have := hB g hg; rwa [cellTemplateHQ_baseCols] at this⟩)
    (fun g hg => ⟨hg, by
      have := hM g hg; rwa [cellTemplateHQ_baseCols, cellTemplateHQ_extCols] at this⟩)
    rfl rfl Q hsat

end Chip

/-! ## 3. The kind lemma and honest completeness (gate level) -/

section Kind
variable {F : Type} [Field F]

theorem eval_cv (e : Env F) (j : ℕ) : (cv j : CoeffExpr F).eval e = e.trace j := rfl

/-- **The kind lemma**: under the five side gates, `kb = 1 ↔ (w = 1 ∧ rank = (0,0))`. -/
theorem sideGates_kind (kb inv w lo hi : ℕ) (e : Env F)
    (h : ∀ g ∈ (sideGates (F := F) kb inv w lo hi), g.eval e = 0) :
    e.trace kb = 1 ↔ (e.trace w = 1 ∧ e.trace lo = 0 ∧ e.trace hi = 0) := by
  have h2 := h (.mul (cv kb) (cv lo)) (by simp [sideGates])
  have h3 := h (.mul (cv kb) (cv hi)) (by simp [sideGates])
  have h4 := h (.mul (.mul (cv w) (notE (cv kb)))
    (.sub (.mul (.add (cv lo) (cv hi)) (cv inv)) (.const 1))) (by simp [sideGates])
  have h5 := h (.mul (cv kb) (notE (cv w))) (by simp [sideGates])
  simp only [CoeffExpr.eval] at h2 h3 h4 h5
  constructor
  · intro hk
    rw [hk] at h2 h3 h5
    simp only [one_mul] at h2 h3 h5
    refine ⟨?_, h2, h3⟩
    linear_combination -h5
  · rintro ⟨hw, hl, hh⟩
    rw [hw, hl, hh] at h4
    linear_combination h4

theorem sideGates_kind_without_fifth_cex (kb inv w lo hi : ℕ) (e : Env F)
    (hw : e.trace w = 0) (hl : e.trace lo = 0) (hh : e.trace hi = 0) (hk : e.trace kb = 1) :
    ∀ g ∈ (sideGates (F := F) kb inv w lo hi).dropLast, g.eval e = 0 := by
  intro g hg
  simp only [sideGates, List.dropLast, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl <;> simp [CoeffExpr.eval, hw, hl, hh, hk]

/-- **Honest completeness (gate level)**: `kb = 0` and `inv = (lo+hi)⁻¹` satisfy every side gate
whenever a weighted child has non-zero rank (`lo + hi ≠ 0`); an atom child (`w = 0`) needs nothing. -/
theorem sideGates_honest (kb inv w lo hi : ℕ) (e : Env F) (hkb : e.trace kb = 0)
    (hinv : e.trace inv = (e.trace lo + e.trace hi)⁻¹)
    (hw : e.trace w = 0 ∨ (e.trace w = 1 ∧ e.trace lo + e.trace hi ≠ 0)) :
    ∀ g ∈ (sideGates (F := F) kb inv w lo hi), g.eval e = 0 := by
  intro g hg
  simp only [sideGates, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl <;> simp only [CoeffExpr.eval, hkb]
  · ring
  · ring
  · ring
  · rcases hw with hw | ⟨hw, hne⟩
    · rw [hw]; ring
    · rw [hw, hinv, mul_inv_cancel₀ hne]; ring
  · ring

/-- Both sides: `kindGates` honest completeness. -/
theorem kindGates_honest (e : Env F) (hkL : e.trace kbL = 0) (hkR : e.trace kbR = 0)
    (hiL : e.trace invL = (e.trace Cell.loL + e.trace Cell.hiL)⁻¹)
    (hiR : e.trace invR = (e.trace Cell.loR + e.trace Cell.hiR)⁻¹)
    (hwL : e.trace Cell.wL = 0 ∨ (e.trace Cell.wL = 1 ∧ e.trace Cell.loL + e.trace Cell.hiL ≠ 0))
    (hwR : e.trace Cell.wR = 0 ∨ (e.trace Cell.wR = 1 ∧ e.trace Cell.loR + e.trace Cell.hiR ≠ 0)) :
    ∀ g ∈ (kindGates (F := F)), g.eval e = 0 := by
  intro g hg
  rcases List.mem_append.mp hg with h | h
  · exact sideGates_honest _ _ _ _ _ e hkL hiL hwL g h
  · exact sideGates_honest _ _ _ _ _ e hkR hiR hwR g h

end Kind

/-! ## 4. F2 receipt: the walk twin DOES test the kind (booleanity), so a wire kind `2` is rejected -/

section F2
variable {F : Type} [Field F]

/-- `walkTemplateHQ` carries the gates `kL(kL-1) = 0`, `kR(kR-1) = 0` (`WalkHC.baseH`, `WalkH.lean:211`). -/
theorem walkBaseH_in_template (δF : F) (kroots : ℕ) :
    ∀ g ∈ (WalkHC.baseH : List (CoeffExpr F)), g ∈ (walkTemplateHQ δF kroots).baseTransition :=
  fun _ hg => List.mem_append_right _ hg

/-- **F2 is FALSE as stated** (gate level): at kind value `kL = 2` (`char F ≠ 2`) the booleanity gate
`kL(kL-1)` evaluates to `2 ≠ 0`, so a trace carrying kind `2` on the walk's `kL` column violates a
`walkTemplateHQ` base gate. -/
theorem walkBaseH_rejects_kind2 (e : Env F) (h2 : (2 : F) ≠ 0) (hk : e.trace WalkHC.kL = 2) :
    ∃ g ∈ (WalkHC.baseH : List (CoeffExpr F)), g.eval e ≠ 0 := by
  refine ⟨boolE (cv WalkHC.kL), by simp [WalkHC.baseH], ?_⟩
  simp only [CoeffExpr.eval, hk]
  norm_num [h2]

end F2

/-! ## 5. A-3r2 item 1: the walk-twin variant `walkChipHQK` (ternary kind gate `k(k-1)(k-2)`) -/

section WalkK
variable {F : Type} [Field F]

/-- Ternary kind gate `k(k-1)(k-2)`. -/
def ternE (x : CoeffExpr F) : CoeffExpr F := .mul (.mul x (.sub x (.const 1))) (.sub x (.const 2))

/-- `WalkHC.baseH` with `boolE kL`, `boolE kR` replaced by the ternary gates. -/
def baseHK : List (CoeffExpr F) := [ternE (cv WalkHC.kL), ternE (cv WalkHC.kR)]

theorem baseHK_deg (kroots : ℕ) : ∀ g ∈ WChip.baseGates (F := F) kroots ++ baseHK, g.degree ≤ 4 := by
  intro g hg
  rcases List.mem_append.mp hg with hg | hg
  · exact walkBase_deg kroots g hg
  · simp [baseHK] at hg; rcases hg with rfl | rfl <;> simp [ternE, CoeffExpr.degree]

/-- **`walkTemplateHQK`**: `walkTemplateHQ` with only `baseH` retyped. -/
def walkTemplateHQK (δF : F) (kroots : ℕ) : ChipTemplate F where
  rounds := 3
  rounds_pos := by decide
  baseColsOf := ![25, 0, 0]
  extColsOf := ![0, 24, 23]
  baseTransition := WChip.baseGates kroots ++ baseHK
  extTransition := []
  mixedTransition := WChip.mixedGates δF kroots ++ WalkHQ.gates δF
  extDeg1 := []
  extDeg3 := []
  equalityChecks := []
  baseTransition_deg := baseHK_deg kroots
  extTransition_deg := by simp
  mixedTransition_deg := WalkHQ.mixed_deg δF kroots
  extDeg1_deg := by simp
  extDeg3_deg := by simp
  equalityChecks_deg := by simp

theorem walkTemplateHQK_baseCols (δF : F) (kroots : ℕ) : (walkTemplateHQK δF kroots).baseCols = 25 := by
  show (∑ r : Fin 3, (![25, 0, 0] : Fin 3 → ℕ) r) = 25
  decide
theorem walkTemplateHQK_extCols (δF : F) (kroots : ℕ) : (walkTemplateHQK δF kroots).extCols = 47 := by
  show (∑ r : Fin 3, (![0, 24, 23] : Fin 3 → ℕ) r) = 47
  decide

/-- Everything except `baseH` is literally unchanged (list equalities). -/
theorem walkHQK_unchanged (δF : F) (kroots : ℕ) :
    (walkTemplateHQK δF kroots).baseTransition = WChip.baseGates kroots ++ baseHK ∧
    (walkTemplateHQ δF kroots).baseTransition = WChip.baseGates kroots ++ WalkHC.baseH ∧
    (walkTemplateHQK δF kroots).mixedTransition = (walkTemplateHQ δF kroots).mixedTransition ∧
    (walkTemplateHQK δF kroots).extTransition = (walkTemplateHQ δF kroots).extTransition ∧
    (walkTemplateHQK δF kroots).extDeg1 = (walkTemplateHQ δF kroots).extDeg1 ∧
    (walkTemplateHQK δF kroots).extDeg3 = (walkTemplateHQ δF kroots).extDeg3 ∧
    (walkTemplateHQK δF kroots).equalityChecks = (walkTemplateHQ δF kroots).equalityChecks ∧
    (walkTemplateHQK δF kroots).baseColsOf = (walkTemplateHQ δF kroots).baseColsOf ∧
    (walkTemplateHQK δF kroots).extColsOf = (walkTemplateHQ δF kroots).extColsOf :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem walkTemplateHQK_width (δF : F) (kroots : ℕ) : (walkTemplateHQK δF kroots).width 3 = 166 := by
  unfold ChipTemplate.width; rw [walkTemplateHQK_baseCols, walkTemplateHQK_extCols]

/-- The `𝕂′` walk twin variant chip (masks `0..2`). -/
noncomputable def walkChipHQK {K : Type} [Field K] [Algebra F K] [FiniteDimensional F K]
    (δF : F) (kroots : ℕ) (b : Basis (Fin 3) F K) {h n : ℕ} (hn : 0 < n)
    (nodes : Fin n → F) (orbit : StrictOrbitDomain F 3 h) (chals pubs : ℕ → K) :
    FixedPreprocessingRAP F where
  rap := expandChip (walkTemplateHQK δF kroots) b (slotVal b 25 chals) (slotVal b 25 pubs) orbit
    (rowNodeSet nodes)
  rounds_pos := by show 0 < 3; omega
  fixedCount := 3
  preprocessingIndex :=
    { toFun := fun j => ⟨j, by
        have := j.isLt
        show (j : ℕ) < 25 + 0 * 3
        omega⟩
      inj' := by intro i j hij; exact Fin.ext (by simpa using congrArg Fin.val hij) }
  preprocessing
    | 0 => firstRowMask nodes
    | 1 => lastRowMask hn nodes
    | 2 => rootRowMaskW nodes kroots

/-- **Width `166`** by `rfl` (as `walkChipHQ`). -/
theorem walkChipHQK_width {K : Type} [Field K] [Algebra F K] [FiniteDimensional F K]
    (δF : F) (kroots : ℕ) (b : Basis (Fin 3) F K) {h n : ℕ} (hn : 0 < n)
    (nodes : Fin n → F) (orbit : StrictOrbitDomain F 3 h) (chals pubs : ℕ → K) :
    (walkChipHQK δF kroots b hn nodes orbit chals pubs).rap.w = 166 :=
  (walkTemplateHQK_width δF kroots : (walkTemplateHQK δF kroots).baseCols + (walkTemplateHQK δF kroots).extCols * 3 = 166)

/-- **Degree `≤ 3`** of the two retyped gates (the template's overall bound stays `≤ 4`). -/
theorem baseHK_deg3 : ∀ g ∈ (baseHK : List (CoeffExpr F)), g.degree ≤ 3 := by
  intro g hg
  simp [baseHK] at hg; rcases hg with rfl | rfl <;> simp [ternE, CoeffExpr.degree]

/-- **Accepts kind 2 (gate level)**: the ternary gates vanish at `k = 2` (also `0`, `1`), whereas the
original booleanity gate rejects `2` (`walkBaseH_rejects_kind2`).  LABEL: gate/template level, not a
full-chip `Satisfies` trace. -/
theorem baseHK_accepts_kind (e : Env F) (hL : e.trace WalkHC.kL = 0 ∨ e.trace WalkHC.kL = 1 ∨ e.trace WalkHC.kL = 2)
    (hR : e.trace WalkHC.kR = 0 ∨ e.trace WalkHC.kR = 1 ∨ e.trace WalkHC.kR = 2) :
    ∀ g ∈ (baseHK : List (CoeffExpr F)), g.eval e = 0 := by
  intro g hg
  simp only [baseHK, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl
  · rcases hL with h | h | h <;> simp [ternE, CoeffExpr.eval, cv, h]
  · rcases hR with h | h | h <;> simp [ternE, CoeffExpr.eval, cv, h]

theorem baseHK_accepts_kind2 (e : Env F) (hL : e.trace WalkHC.kL = 2) (hR : e.trace WalkHC.kR = 2) :
    ∀ g ∈ (baseHK : List (CoeffExpr F)), g.eval e = 0 :=
  baseHK_accepts_kind e (Or.inr (Or.inr hL)) (Or.inr (Or.inr hR))

/-- **Honest kinds `∈ {0,1}` (gate level)**: on any env with boolean kinds, the variant's base gates
hold iff the original's do (so the honest walk traces keep satisfying the template's base gates). -/
theorem walkBaseHQK_iff_of_bool (δF : F) (kroots : ℕ) (e : Env F)
    (hL : e.trace WalkHC.kL = 0 ∨ e.trace WalkHC.kL = 1) (hR : e.trace WalkHC.kR = 0 ∨ e.trace WalkHC.kR = 1) :
    (∀ g ∈ (walkTemplateHQ δF kroots).baseTransition, g.eval e = 0) ↔
    (∀ g ∈ (walkTemplateHQK δF kroots).baseTransition, g.eval e = 0) := by
  have hK := baseHK_accepts_kind e (by tauto) (by tauto)
  have hB : ∀ g ∈ (WalkHC.baseH : List (CoeffExpr F)), g.eval e = 0 := by
    intro g hg
    simp only [WalkHC.baseH, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl
    · rcases hL with h | h <;> simp [boolE, CoeffExpr.eval, cv, h]
    · rcases hR with h | h <;> simp [boolE, CoeffExpr.eval, cv, h]
  constructor
  · intro h g hg
    rcases List.mem_append.mp hg with hg | hg
    · exact h g (List.mem_append_left _ hg)
    · exact hK g hg
  · intro h g hg
    rcases List.mem_append.mp hg with hg | hg
    · exact h g (List.mem_append_left _ hg)
    · exact hB g hg

end WalkK
