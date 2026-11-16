/-
  Nock/NockVMROM/Thm54/VclL/Handle/AtomChipHQL.lean

  * `gL := isL · c_out`, `atomGatesL := atomGates ++ [gL]`, `atomTemplateHQL` = `atomTemplateHQ` with
    `atomGatesL` in place of `atomGates` (every other field verbatim).  **Width `349` by `rfl`**
    (`atomChipHQL_width`), degree `≤ 4` (`gL` has degree `2`, `gL_deg`).
  * **`atomChipHQL_sat_iff`**: for a variant trace `Q` and an `atomChipHQ` trace `Q0` with the same `349` columns,
    `atomChipHQL` accepts `Q` iff `atomChipHQ` accepts `Q0` and `gL` vanishes at every row.  `toHQ` / `ofHQ` read a
    trace of one chip as the other's (`aEF_toHQ`: same row environments).  So every soundness lemma stated at
    `atomChipHQ` applies to `toHQ Q` of an `atomChipHQL`-accepted `Q` (`atomChipHQL_sat`, `atomChipHQL_bind`), and
    the restrictions to the cell chips follow (`atomChipHQL_restrict_sat`, `atomChipHQL_restrict_cell_sat`).
  * **`cout_last`**: on an accepted trace the last row's `c_out` is `0`.
  * **Honest acceptance** (`atomChipHQL_accepts_honest`): J-8b's `HonestA8.atomChipHQ_accepts_honest` (by name)
    plus `hlast`: the honest last row carries no carry-out.  The accepted trace is `ofHQ` of J-8b's
    `atomTraceHQ`.  `hlast` is a named honest-side condition (as `hbase` is in `HonestA8`); that the honest
    generator meets it (it appends the carry's top-limb row, so a carrying inc row is never last) is an
    ARGUMENT, not compiled here.
  * `gL_load_bearing`: a row with `isL = 1`, `c_out = 1` evaluates `gL` to `1`.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.HonestA8
import Nock.NockVMROM.Thm54.VclL.Handle.AtomServedQ

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.AtomChipHQL

open Nock Nock.Reified Nock.Framework
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.VclL.Handle Nock.NockVMROM.Thm54.VclL.Handle.RangeHQ
open Nock.NockVMROM.Thm54.VclL.Handle.AtomChipHQ Nock.NockVMROM.Thm54.VclL.Handle.QGates
open Module
open scoped Polynomial

section Gates
variable {F : Type} [Field F]

/-- **The ruled gate** `isL · c_out = 0`: the last row carries no carry-out. -/
def gL : CoeffExpr F := .mul (cv Cell.isL) (cv cout)

/-- The atom table's added base gates with `gL`. -/
def atomGatesL : List (CoeffExpr F) := atomGates ++ [gL]

theorem gL_deg : (gL : CoeffExpr F).degree ≤ 2 := by
  simp [gL, cv, CoeffExpr.degree]

theorem atomGatesL_deg : ∀ g ∈ (atomGatesL (F := F)), g.degree ≤ 4 := by
  intro g hg
  rcases List.mem_append.mp hg with h | h
  · exact atomGates_deg g h
  · rw [List.mem_singleton.mp h]; exact le_trans gL_deg (by norm_num)

theorem gL_below : colsBelow 205 (gL : CoeffExpr F) = true := by
  simp [gL, cv, colsBelow, Cell.isL, cout]

/-- **The atom table template with `gL`** (`atomTemplateHQ` otherwise verbatim). -/
def atomTemplateHQL (δF : F) : ChipTemplate F where
  rounds := 3
  rounds_pos := by decide
  baseColsOf := ![205, 0, 0]
  extColsOf := ![0, 18, 30]
  baseTransition := Cell.baseGates ++ atomGatesL
  extTransition := []
  mixedTransition := Cell.mixedGates δF ++ CellHQ.gates δF ++ atomMixed δF
  extDeg1 := []
  extDeg3 := []
  equalityChecks := []
  baseTransition_deg := by
    intro g hg
    rcases List.mem_append.mp hg with h | h
    · exact cellBase_deg g h
    · exact atomGatesL_deg g h
  extTransition_deg := by simp
  mixedTransition_deg := by
    intro g hg
    rcases List.mem_append.mp hg with h | h
    · exact CellHQ.mixed_deg δF g h
    · exact atomMixed_deg δF g h
  extDeg1_deg := by simp
  extDeg3_deg := by simp
  equalityChecks_deg := by simp

theorem atomTemplateHQL_baseCols (δF : F) : (atomTemplateHQL δF).baseCols = 205 := by
  show (∑ r : Fin 3, (![205, 0, 0] : Fin 3 → ℕ) r) = 205
  decide

theorem atomTemplateHQL_extCols (δF : F) : (atomTemplateHQL δF).extCols = 48 := by
  show (∑ r : Fin 3, (![0, 18, 30] : Fin 3 → ℕ) r) = 48
  decide

/-- Every base gate of the variant reads columns `< 205`. -/
theorem atomGatesL_below : ∀ g ∈ (atomGatesL (F := F)), colsBelow 205 g = true := by
  intro g hg
  rcases List.mem_append.mp hg with h | h
  · exact atomGates_below g h
  · rw [List.mem_singleton.mp h]; exact gL_below

end Gates

section Chip
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]

/-- **`atomChipHQL`** (masks at `0`, `1`, as `atomChipHQ`). -/
noncomputable def atomChipHQL (δF : F) (b : Basis (Fin 3) F K) {h n : ℕ} (hn : 0 < n)
    (nodes : Fin n → F) (orbit : StrictOrbitDomain F 3 h) (chals pubs : ℕ → K) :
    FixedPreprocessingRAP F where
  rap := expandChip (atomTemplateHQL δF) b (slotVal b 205 chals) (slotVal b 205 pubs) orbit
    (rowNodeSet nodes)
  rounds_pos := by show 0 < 3; omega
  fixedCount := 2
  preprocessingIndex :=
    { toFun := fun j => ⟨j, by
        have := j.isLt
        show (j : ℕ) < 205 + 0 * 3
        omega⟩
      inj' := by intro i j hij; exact Fin.ext (by simpa using congrArg Fin.val hij) }
  preprocessing
    | 0 => firstRowMask nodes
    | 1 => lastRowMask hn nodes

variable (δF : F) (b : Basis (Fin 3) F K) {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F)
  (orbit : StrictOrbitDomain F 3 h) (chals pubs : ℕ → K)

set_option maxRecDepth 20000 in
/-- **Width `349`** (`205 + 48·3`), by `rfl`: the gate adds no column. -/
theorem atomChipHQL_width : (atomChipHQL δF b hn nodes orbit chals pubs).rap.w = 349 := rfl

/-- A trace of the variant read as an `atomChipHQ` trace (same `349` columns). -/
def toHQ (Q : Fin (atomChipHQL δF b hn nodes orbit chals pubs).rap.w → F[X]) :
    Fin (atomChipHQ δF b hn nodes orbit chals pubs).rap.w → F[X] :=
  fun j => Q ⟨j, lt_of_lt_of_eq (lt_of_lt_of_eq j.2 (atomChipHQ_width δF b hn nodes orbit chals pubs))
    (atomChipHQL_width δF b hn nodes orbit chals pubs).symm⟩

/-- An `atomChipHQ` trace read as a variant trace (same `349` columns). -/
def ofHQ (Q0 : Fin (atomChipHQ δF b hn nodes orbit chals pubs).rap.w → F[X]) :
    Fin (atomChipHQL δF b hn nodes orbit chals pubs).rap.w → F[X] :=
  fun j => Q0 ⟨j, lt_of_lt_of_eq (lt_of_lt_of_eq j.2 (atomChipHQL_width δF b hn nodes orbit chals pubs))
    (atomChipHQ_width δF b hn nodes orbit chals pubs).symm⟩

/-- Two traces with the same `349` columns induce the same row environments. -/
theorem envOfTrace_congr349 {w w' : ℕ} (Q : Fin w → F[X]) (Q' : Fin w' → F[X]) (hw : w = 349) (hw' : w' = 349)
    (hQ : ∀ j (hj : j < 349), Q ⟨j, hw ▸ hj⟩ = Q' ⟨j, hw' ▸ hj⟩) (ω x : F) (cv pv : ℕ → F) :
    Reify.envOfTrace Q ω x cv pv = Reify.envOfTrace Q' ω x cv pv := by
  subst hw hw'
  have : Q = Q' := funext fun j => hQ j j.2
  rw [this]

theorem aEF_toHQ (Q : Fin (atomChipHQL δF b hn nodes orbit chals pubs).rap.w → F[X]) (i : Fin n) :
    AtomServedQ.aEF b nodes orbit chals pubs (toHQ δF b hn nodes orbit chals pubs Q) i =
      AtomServedQ.aEF b nodes orbit chals pubs Q i := by
  apply envOfTrace_congr349 _ _ (atomChipHQ_width δF b hn nodes orbit chals pubs)
    (atomChipHQL_width δF b hn nodes orbit chals pubs)
  intro j hj
  simp only [toHQ]

theorem baseL_eq : (atomTemplateHQL δF).baseTransition = Cell.baseGates ++ atomGatesL := rfl
theorem baseH_eq : (atomTemplateHQ δF).baseTransition = Cell.baseGates ++ atomGates := rfl
theorem mixL_eq : (atomTemplateHQL δF).mixedTransition = Cell.mixedGates δF ++ CellHQ.gates δF ++ atomMixed δF := rfl
theorem mixH_eq : (atomTemplateHQ δF).mixedTransition = Cell.mixedGates δF ++ CellHQ.gates δF ++ atomMixed δF := rfl
theorem eqL_eq : (atomTemplateHQL δF).equalityChecks = [] := rfl
theorem eqH_eq : (atomTemplateHQ δF).equalityChecks = [] := rfl
theorem extL_eq : (atomTemplateHQL δF).extTransition ++ (atomTemplateHQL δF).extDeg1 ++
    (atomTemplateHQL δF).extDeg3 = [] := rfl
theorem extH_eq : (atomTemplateHQ δF).extTransition ++ (atomTemplateHQ δF).extDeg1 ++
    (atomTemplateHQ δF).extDeg3 = [] := rfl
theorem colL_eq : (atomTemplateHQL δF).col0 3 = fun _ idx => 205 + 3 * idx := by
  funext v idx; simp [ChipTemplate.col0, atomTemplateHQL_baseCols]
theorem colH_eq : (atomTemplateHQ δF).col0 3 = fun _ idx => 205 + 3 * idx := by
  funext v idx; simp [ChipTemplate.col0, atomTemplateHQ_baseCols]

attribute [local irreducible] atomGatesL

/-- **The variant against `atomChipHQ`**: for traces `Q` (variant) and `Q0` (`atomChipHQ`) with the same `349`
columns, `atomChipHQL` accepts `Q` iff `atomChipHQ` accepts `Q0` and `gL` vanishes at every row. -/
theorem atomChipHQL_sat_iff (Q : Fin (atomChipHQL δF b hn nodes orbit chals pubs).rap.w → F[X])
    (Q0 : Fin (atomChipHQ δF b hn nodes orbit chals pubs).rap.w → F[X])
    (hQ : ∀ j (hj : j < 349), Q ⟨j, (atomChipHQL_width δF b hn nodes orbit chals pubs) ▸ hj⟩ =
      Q0 ⟨j, (atomChipHQ_width δF b hn nodes orbit chals pubs) ▸ hj⟩) :
    (atomChipHQL δF b hn nodes orbit chals pubs).rap.Satisfies Q ↔
      (atomChipHQ δF b hn nodes orbit chals pubs).rap.Satisfies Q0 ∧
        ∀ i : Fin n, (gL : CoeffExpr F).eval (AtomServedQ.aEF b nodes orbit chals pubs Q i) = 0 := by
  have henv : ∀ x, Reify.envOfTrace
        (w := (expandChip (atomTemplateHQL δF) b (slotVal b 205 chals) (slotVal b 205 pubs) orbit
          (rowNodeSet nodes)).w) Q orbit.ω x (slotVal b 205 chals) (slotVal b 205 pubs) =
      Reify.envOfTrace
        (w := (expandChip (atomTemplateHQ δF) b (slotVal b 205 chals) (slotVal b 205 pubs) orbit
          (rowNodeSet nodes)).w) Q0 orbit.ω x (slotVal b 205 chals) (slotVal b 205 pubs) := fun x =>
    envOfTrace_congr349 Q Q0 (atomChipHQL_width δF b hn nodes orbit chals pubs)
      (atomChipHQ_width δF b hn nodes orbit chals pubs) hQ _ _ _ _
  have eL := expandChip_satisfies_iff_language (atomTemplateHQL δF) b (slotVal b 205 chals)
    (slotVal b 205 pubs) orbit (rowNodeSet nodes) Q
  have eH := expandChip_satisfies_iff_language (atomTemplateHQ δF) b (slotVal b 205 chals)
    (slotVal b 205 pubs) orbit (rowNodeSet nodes) Q0
  rw [baseL_eq, eqL_eq, extL_eq, mixL_eq, colL_eq] at eL
  rw [baseH_eq, eqH_eq, extH_eq, mixH_eq, colH_eq] at eH
  constructor
  · intro hsat
    have hl := eL.mp hsat
    refine ⟨eH.mpr fun x hx => ?_, fun i => ?_⟩
    · obtain ⟨h1, -, -, h4⟩ := hl x hx
      rw [henv x] at h1 h4
      refine ⟨fun g hg => h1 g ?_, by simp, by simp, h4⟩
      unfold atomGatesL
      rcases List.mem_append.mp hg with h | h
      · exact List.mem_append_left _ h
      · exact List.mem_append_right _ (List.mem_append_left _ h)
    · have h1 := (hl (nodes i) (mem_rowNodeSet nodes i)).1
      exact h1 gL (List.mem_append_right _ (by unfold atomGatesL; simp))
  · rintro ⟨hsat, hL⟩
    have hl := eH.mp hsat
    refine eL.mpr fun x hx => ?_
    obtain ⟨h1, -, -, h4⟩ := hl x hx
    rw [← henv x] at h1 h4
    refine ⟨fun g hg => ?_, by simp, by simp, h4⟩
    obtain ⟨i, rfl⟩ := (mem_rowNodeSet_iff nodes x).mp hx
    unfold atomGatesL at hg
    rcases List.mem_append.mp hg with h | h
    · exact h1 g (List.mem_append_left _ h)
    · rcases List.mem_append.mp h with h | h
      · exact h1 g (List.mem_append_right _ h)
      · rw [List.mem_singleton.mp h]; exact hL i

/-- An accepted variant trace is `atomChipHQ`-accepted as `toHQ`. -/
theorem atomChipHQL_sat (Q : Fin (atomChipHQL δF b hn nodes orbit chals pubs).rap.w → F[X])
    (hsat : (atomChipHQL δF b hn nodes orbit chals pubs).rap.Satisfies Q) :
    (atomChipHQ δF b hn nodes orbit chals pubs).rap.Satisfies (toHQ δF b hn nodes orbit chals pubs Q) :=
  ((atomChipHQL_sat_iff δF b hn nodes orbit chals pubs Q _ (fun j hj => rfl)).mp hsat).1

/-- `gL` at every row of an accepted variant trace. -/
theorem atomChipHQL_gL (Q : Fin (atomChipHQL δF b hn nodes orbit chals pubs).rap.w → F[X])
    (hsat : (atomChipHQL δF b hn nodes orbit chals pubs).rap.Satisfies Q) (i : Fin n) :
    (gL : CoeffExpr F).eval (AtomServedQ.aEF b nodes orbit chals pubs (toHQ δF b hn nodes orbit chals pubs Q) i) = 0 := by
  rw [aEF_toHQ]
  exact ((atomChipHQL_sat_iff δF b hn nodes orbit chals pubs Q _ (fun j hj => rfl)).mp hsat).2 i

/-- The preprocessing transfers. -/
theorem atomChipHQL_bind (Q : Fin (atomChipHQL δF b hn nodes orbit chals pubs).rap.w → F[X])
    (hbind : (atomChipHQL δF b hn nodes orbit chals pubs).BindsPreprocessing Q) :
    (atomChipHQ δF b hn nodes orbit chals pubs).BindsPreprocessing (toHQ δF b hn nodes orbit chals pubs Q) := by
  have h0 := hbind ⟨0, by show 0 < 2; omega⟩
  have h1 := hbind ⟨1, by show 1 < 2; omega⟩
  have p0 : (atomChipHQL δF b hn nodes orbit chals pubs).preprocessing ⟨0, by show 0 < 2; omega⟩ =
    firstRowMask nodes := rfl
  have p1 : (atomChipHQL δF b hn nodes orbit chals pubs).preprocessing ⟨1, by show 1 < 2; omega⟩ =
    lastRowMask hn nodes := rfl
  rw [p0] at h0
  rw [p1] at h1
  intro j
  fin_cases j
  · exact h0
  · exact h1

/-- **Restriction** to `cellChipHQ` (through `atomChipHQ`). -/
theorem atomChipHQL_restrict_sat (Q : Fin (atomChipHQL δF b hn nodes orbit chals pubs).rap.w → F[X])
    (hsat : (atomChipHQL δF b hn nodes orbit chals pubs).rap.Satisfies Q) :
    (cellChipHQ δF b hn nodes orbit chals pubs).rap.Satisfies
      (restrictAtomQ δF b hn nodes orbit chals pubs (toHQ δF b hn nodes orbit chals pubs Q)) :=
  atomChipHQ_restrict_sat δF b hn nodes orbit chals pubs _ (atomChipHQL_sat δF b hn nodes orbit chals pubs Q hsat)

/-- **Restriction** to the original `cellChip` (`225` columns, the chip T1 is stated on). -/
theorem atomChipHQL_restrict_cell_sat (Q : Fin (atomChipHQL δF b hn nodes orbit chals pubs).rap.w → F[X])
    (hsat : (atomChipHQL δF b hn nodes orbit chals pubs).rap.Satisfies Q) :
    (cellChip δF b hn nodes orbit chals pubs).rap.Satisfies
      (restrictAtomCell δF b hn nodes orbit chals pubs (toHQ δF b hn nodes orbit chals pubs Q)) :=
  atomChipHQ_restrict_cell_sat δF b hn nodes orbit chals pubs _ (atomChipHQL_sat δF b hn nodes orbit chals pubs Q hsat)

/-- **The last row carries no carry-out** on an accepted variant trace. -/
theorem cout_last [Fintype K] [Fact (¬ IsSquare (algebraMap F K δF))] (Q : Fin (atomChipHQL δF b hn nodes orbit chals pubs).rap.w → F[X])
    (hsat : (atomChipHQL δF b hn nodes orbit chals pubs).rap.Satisfies Q)
    (hbind : (atomChipHQL δF b hn nodes orbit chals pubs).BindsPreprocessing Q)
    (hinj : Function.Injective nodes) (i : Fin n) (hi : (i : ℕ) = n - 1) :
    (AtomServedQ.aEF b nodes orbit chals pubs (toHQ δF b hn nodes orbit chals pubs Q) i).trace cout = 0 := by
  have hL := atomChipHQL_gL δF b hn nodes orbit chals pubs Q hsat i
  have hm := (AtomServedQ.atom_masks δF b hn nodes orbit chals pubs _
    (atomChipHQL_bind δF b hn nodes orbit chals pubs Q hbind) hinj i).2
  simp only [gL, cv, CoeffExpr.eval, hm, if_pos hi, one_mul] at hL
  exact hL

/-- **Negative control**: `gL` is `1` at a row with `isL = 1`, `c_out = 1`. -/
theorem gL_load_bearing (e : Env F) (h1 : e.trace Cell.isL = 1) (h2 : e.trace cout = 1) :
    (gL : CoeffExpr F).eval e = 1 := by
  simp [gL, cv, CoeffExpr.eval, h1, h2]

end Chip

/-! ## Honest acceptance (J-8b `HonestA8`, by name) -/

section Honest
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [Fintype K]
  (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))] (b : Basis (Fin 3) F K) {h n : ℕ} (hn : 0 < n)
  (nodes : Fin n → F) (orbit : StrictOrbitDomain F 3 h) (chals pubs : ℕ → K)
  (col newB : ℕ → Fin n → F)

attribute [local irreducible] atomGatesL

set_option maxHeartbeats 1000000 in
/-- **`atomChipHQL_accepts_honest`**: `HonestA8.atomChipHQ_accepts_honest`'s hypotheses plus `hlast` (the honest
last row has `c_out = 0`) give acceptance by the variant of the same honest trace `HonestA8.atomTraceHQ`
(read as a variant trace, `ofHQ`). -/
theorem atomChipHQL_accepts_honest (hinj : Function.Injective nodes)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω)
    (hsat0 : (cellChipHQ δF b hn nodes orbit chals pubs).rap.Satisfies (honestQ hn nodes col _))
    (hbase : ∀ i, ∀ g ∈ (atomGates (F := F)),
      g.eval (HonestA8.EZ δF b hn nodes orbit chals pubs col newB i) = 0)
    (hz1 : ∀ i, HonestA8.dMB δF b hn nodes orbit chals pubs col newB i ≠ 0)
    (hz2 : ∀ i, HonestA8.dC δF b hn nodes orbit chals pubs col newB i ≠ 0)
    (hz3 : ∀ i, HonestA8.dMI δF b hn nodes orbit chals pubs col newB i ≠ 0)
    (hpMB : Quad.mk _ (pubs pubMB) (pubs (pubMB + 1)) = ∑ j ∈ Finset.range n,
      liftQ δF (HonestA8.cNat j (newB mb)) *
        (HonestA8.dNat δF (HonestA8.dMB δF b hn nodes orbit chals pubs col newB) j)⁻¹)
    (hpC : Quad.mk _ (pubs pubC) (pubs (pubC + 1)) = ∑ j ∈ Finset.range n,
      liftQ δF (HonestA8.cNat j (newB inc)) *
        (HonestA8.dNat δF (HonestA8.dC δF b hn nodes orbit chals pubs col newB) j)⁻¹)
    (hpMI : Quad.mk _ (pubs pubMI) (pubs (pubMI + 1)) = ∑ j ∈ Finset.range n,
      liftQ δF (HonestA8.cNat j (newB mi)) *
        (HonestA8.dNat δF (HonestA8.dMI δF b hn nodes orbit chals pubs col newB) j)⁻¹)
    (hlast : ∀ i : Fin n, (i : ℕ) + 1 = n → newB cout i = 0) :
    (atomChipHQL δF b hn nodes orbit chals pubs).rap.Satisfies
      (ofHQ δF b hn nodes orbit chals pubs (HonestA8.atomTraceHQ δF b hn nodes orbit chals pubs col newB)) := by
  have hH := HonestA8.atomChipHQ_accepts_honest δF b hn nodes orbit chals pubs col newB hinj hadj hsat0 hbase
    hz1 hz2 hz3 hpMB hpC hpMI
  refine (atomChipHQL_sat_iff δF b hn nodes orbit chals pubs
    (ofHQ δF b hn nodes orbit chals pubs (HonestA8.atomTraceHQ δF b hn nodes orbit chals pubs col newB))
    (HonestA8.atomTraceHQ δF b hn nodes orbit chals pubs col newB) (fun j hj => rfl)).mpr ⟨hH, fun i => ?_⟩
  have hE : AtomServedQ.aEF b nodes orbit chals pubs
      (ofHQ δF b hn nodes orbit chals pubs (HonestA8.atomTraceHQ δF b hn nodes orbit chals pubs col newB)) i =
      HonestA8.E1 δF b hn nodes orbit chals pubs col newB i := by
    unfold HonestA8.E1
    apply envOfTrace_congr349 _ _ (atomChipHQL_width δF b hn nodes orbit chals pubs) rfl
    intro j hj
    exact congrArg (honestQ hn nodes (HonestA8.colA δF b hn nodes orbit chals pubs col newB) 349) (Fin.ext rfl)
  rw [hE]
  have hL := HonestA8.E1_isL δF b hn nodes orbit chals pubs col newB hinj i
  have hC := (HonestA8.E1_mult δF b hn nodes orbit chals pubs col newB hinj hadj i cout
    (by simp [cout]) (by simp [cout])).1
  simp only [gL, cv, CoeffExpr.eval, hL, hC]
  by_cases hl : (i : ℕ) + 1 = n
  · rw [if_pos hl]
    simp [HonestA8.cNat, i.2, hlast i hl]
  · rw [if_neg hl, zero_mul]

end Honest

end Nock.NockVMROM.Thm54.VclL.Handle.AtomChipHQL
