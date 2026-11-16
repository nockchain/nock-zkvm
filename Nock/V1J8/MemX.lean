/-
  Nock/V1J8/MemX.lean

  Every J-8 memory-side chip (`cellChipHQKW`, `walkChipJ8`, `atomChipHQ`, `atomChipHQL`, `walkChipHQK`,
  `jetChipJ8`) is `expandChip Tm b (slotVal b B chals) (slotVal b B pubs) orbit (rowNodeSet nodes)` with
  `B = Tm.baseCols` and verifier-fixed columns `j ↦ j`.  This module does the template once:

  * `kenvB B`: the `K3` environment of a base environment at offset `B` (`𝕂` column `i` at `B + 3 i`);
    `evalEZ` (an `Expr` over `K3`) with `toK_evalEZ`; `ext_eval` / `mixB_eval`: a compiled coordinate gate is a
    limb of the source value.
  * `srcM Tm` (the template's gates as SOURCE gates), `srcM_expand : (srcM Tm).flatMap (expandM _) =
    Tm.allGates powerBasis3`; `srcOK_iff`, `rowOK_iff`.
  * `TabM` (rows, `K3` coins and publics, the fixed columns), **`checkM`** (computable) and `checkM_iff`.
  * **`chipM_iff`**: for any `FixedPreprocessingRAP` whose RAP has the template's width, the table's `ω` and row
    set, the expanded gates at the slot-encoded coins (`expandChip_C`), and the table's fixed columns,
    `SatisfiesWithPreprocessing R P ↔ checkM Tm T = true` on the row interpolants.

  Per chip: `Nock/V1J8/MemChips.lean`.
-/
import Nock.V1J8.CompX

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Nock.V1J8.MemX

open Nock Nock.Reified Nock.Framework Nock.TraceGenExe Nock.Field Polynomial
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP (slotVal)
open Nock.V1Check Nock.V1J8.Exe
open Nock.V1J8.CompX (readK mapEnvK coord_readK powK toK_powK evalMZ toK_evalMZ zero3 zero3_iff ofFn_get_map
  mapC_id firstMaskE lastMaskE)
open Nock.NockVMROM.Thm54.StrictExtension (StrictOrbitDomain)

/-! ## 1. `𝕂` values at a base offset, and the `Expr` evaluator -/

/-- The `𝕂` column layout of a template with `B` base columns (`= ChipTemplate.col0 3`). -/
def col0B (B : ℕ) : VarKind → ℕ → ℕ := fun _ idx => B + 3 * idx

/-- The `K3` environment of a base environment at offset `B`. -/
def kenvB (B : ℕ) (e : Env (ZMod p)) : Env K3 :=
  ⟨fun i => readK e.trace (B + 3 * i), fun i => readK e.traceNext (B + 3 * i),
    fun i => readK e.chal (B + 3 * i), fun i => readK e.pub (B + 3 * i)⟩

theorem isCoordEnv_kenvB (B : ℕ) (e : Env (ZMod p)) :
    IsCoordEnv powerBasis3 (col0B B) (mapEnvK (kenvB B e)) e where
  trace := fun idx k => (coord_readK e.trace (B + 3 * idx) k).symm
  traceNext := fun idx k => (coord_readK e.traceNext (B + 3 * idx) k).symm
  chal := fun idx k => (coord_readK e.chal (B + 3 * idx) k).symm
  pub := fun idx k => (coord_readK e.pub (B + 3 * idx) k).symm

/-- **The executable evaluator of an `𝕂`-valued `Expr` gate** over `K3`. -/
def evalEZ (eK : Env K3) : Expr → K3
  | .Var .traceCur i => eK.trace i
  | .Var .traceNext i => eK.traceNext i
  | .Var .challenge i => eK.chal i
  | .Var .publicVal i => eK.pub i
  | .Const c => g3 (Gold.ofZ (c : ZMod p))
  | .Add x y => evalEZ eK x + evalEZ eK y
  | .Sub x y => evalEZ eK x - evalEZ eK y
  | .Mul x y => evalEZ eK x * evalEZ eK y
  | .Neg x => - evalEZ eK x
  | .Pow x n => powK (evalEZ eK x) n

theorem toK_evalEZ (eK : Env K3) (g : Expr) : K3.toK (evalEZ eK g) = g.eval (mapEnvK eK) := by
  induction g with
  | Var k i => cases k <;> rfl
  | Const c => simp only [evalEZ, Expr.eval, toK_g3, Gold.toZ_ofZ, map_intCast]
  | Add x y ihx ihy => simp only [evalEZ, Expr.eval, K3.toK_add, ihx, ihy]
  | Sub x y ihx ihy => simp only [evalEZ, Expr.eval, K3.toK_sub, ihx, ihy]
  | Mul x y ihx ihy => simp only [evalEZ, Expr.eval, K3.toK_mul, ihx, ihy]
  | Neg x ihx => simp only [evalEZ, Expr.eval, K3.toK_neg, ihx]
  | Pow x n ihx => simp only [evalEZ, Expr.eval, toK_powK, ihx]

/-- **A compiled `Expr` coordinate gate is the limb of the source value.** -/
theorem ext_eval (B : ℕ) (e : Env (ZMod p)) (g : Expr) (k : Fin 3) :
    (coordinateCompile powerBasis3 (col0B B) g k).eval e =
      ![(evalEZ (kenvB B e) g).c0.toZ, (evalEZ (kenvB B e) g).c1.toZ, (evalEZ (kenvB B e) g).c2.toZ] k := by
  rw [← coordinateCompile_eval powerBasis3 (col0B B) (isCoordEnv_kenvB B e) g k, ← toK_evalEZ,
    coord_powerBasis3_toK]

/-- **A compiled mixed coordinate gate is the limb of the source value.** -/
theorem mixB_eval (B : ℕ) (e : Env (ZMod p)) (m : MixedExpr (ZMod p)) (k : Fin 3) :
    (mixedCompile powerBasis3 (col0B B) m k).eval e =
      ![(evalMZ (kenvB B e) e m).c0.toZ, (evalMZ (kenvB B e) e m).c1.toZ, (evalMZ (kenvB B e) e m).c2.toZ] k := by
  rw [← mixedCompile_eval powerBasis3 (col0B B) (isCoordEnv_kenvB B e) m k, ← toK_evalMZ,
    coord_powerBasis3_toK]

/-! ## 2. Source gates of a template -/

/-- A source gate: a base gate, an `𝕂`-valued `Expr` gate, or a mixed `𝕂`-valued gate. -/
inductive SGM where
  | base : CoeffExpr (ZMod p) → SGM
  | ext : Expr → SGM
  | mix : MixedExpr (ZMod p) → SGM

/-- The compiled coordinate gates of a source gate (power basis, offset `B`). -/
noncomputable def expandM (B : ℕ) : SGM → List (CoeffExpr (ZMod p))
  | .base g => [g]
  | .ext g => coordVec powerBasis3 (col0B B) g
  | .mix m => mixedCoordVec powerBasis3 (col0B B) m

/-- **The template's gates as source gates**, in `allGates` order. -/
def srcM (Tm : ChipTemplate (ZMod p)) : List SGM :=
  Tm.baseTransition.map SGM.base ++ Tm.extTransition.map SGM.ext ++ Tm.mixedTransition.map SGM.mix ++
    Tm.extDeg1.map SGM.ext ++ Tm.extDeg3.map SGM.ext ++ Tm.equalityChecks.map SGM.base

theorem fm_base (B : ℕ) (A : List (CoeffExpr (ZMod p))) : (A.map SGM.base).flatMap (expandM B) = A := by
  induction A with
  | nil => rfl
  | cons g l ih => simp only [List.map_cons, List.flatMap_cons, ih]; rfl

theorem fm_ext (B : ℕ) (A : List Expr) :
    (A.map SGM.ext).flatMap (expandM B) = A.flatMap (coordVec powerBasis3 (col0B B)) := by
  induction A with
  | nil => rfl
  | cons g l ih => simp only [List.map_cons, List.flatMap_cons, ih]; rfl

theorem fm_mix (B : ℕ) (A : List (MixedExpr (ZMod p))) :
    (A.map SGM.mix).flatMap (expandM B) = A.flatMap (mixedCoordVec powerBasis3 (col0B B)) := by
  induction A with
  | nil => rfl
  | cons g l ih => simp only [List.map_cons, List.flatMap_cons, ih]; rfl

/-- **The chip's gate list is the expansion of the source gates.** -/
theorem srcM_expand (Tm : ChipTemplate (ZMod p)) :
    (srcM Tm).flatMap (expandM Tm.baseCols) = Tm.allGates powerBasis3 := by
  unfold srcM
  simp only [List.flatMap_append, fm_base, fm_ext, fm_mix]
  rfl

/-- One source gate at one row. -/
def srcOK (B : ℕ) (e : Env (ZMod p)) : SGM → Bool
  | .base g => decide (g.eval e = 0)
  | .ext g => zero3 (evalEZ (kenvB B e) g)
  | .mix m => zero3 (evalMZ (kenvB B e) e m)

theorem srcOK_iff (B : ℕ) (e : Env (ZMod p)) (s : SGM) :
    srcOK B e s = true ↔ ∀ g ∈ expandM B s, g.eval e = 0 := by
  cases s with
  | base g => simp [srcOK, expandM]
  | ext g =>
      simp only [srcOK, expandM, coordVec, List.forall_mem_map, List.mem_finRange, true_implies, ext_eval]
      exact zero3_iff _
  | mix m =>
      simp only [srcOK, expandM, mixedCoordVec, List.forall_mem_map, List.mem_finRange, true_implies, mixB_eval]
      exact zero3_iff _

theorem rowOK_iff (Tm : ChipTemplate (ZMod p)) (e : Env (ZMod p)) :
    (srcM Tm).all (srcOK Tm.baseCols e) = true ↔ ∀ g ∈ Tm.allGates powerBasis3, g.eval e = 0 := by
  rw [← srcM_expand, List.all_eq_true]
  simp only [List.mem_flatMap]
  constructor
  · rintro h g ⟨s, hs, hg⟩
    exact (srcOK_iff _ e s).mp (h s hs) g hg
  · intro h s hs
    exact (srcOK_iff _ e s).mpr fun g hg => h g ⟨s, hs, hg⟩

/-! ## 3. Slot-encoded coins and publics -/

/-- Limb `k` of a `K3`. -/
def limb (a : K3) (k : ℕ) : ZMod p := if k = 0 then a.c0.toZ else if k = 1 then a.c1.toZ else a.c2.toZ

theorem limb_eq (a : K3) (k : Fin 3) : limb a k = ![a.c0.toZ, a.c1.toZ, a.c2.toZ] k := by
  fin_cases k <;> rfl

/-- **`slotVal`, executable**: `𝕂` value `i` at slots `B + 3 i + k`. -/
def slotE (B : ℕ) (v : ℕ → K3) (n : ℕ) : ZMod p :=
  if B ≤ n then limb (v ((n - B) / 3)) ((n - B) % 3) else 0

theorem slotE_eq (B : ℕ) (v : ℕ → K3) (n : ℕ) :
    slotE B v n = slotVal powerBasis3 B (fun i => K3.toK (v i)) n := by
  unfold slotE slotVal
  split_ifs with h
  · rw [coord_powerBasis3_toK, ← limb_eq]
  · rfl

/-- `zero3` is `= 0` in `𝕂`. -/
theorem zero3_iff_toK (a : K3) : zero3 a = true ↔ K3.toK a = 0 := by
  rw [show (0 : KC) = K3.toK 0 from K3.toK_zero.symm, K3.toK_injective.eq_iff]
  obtain ⟨a0, a1, a2⟩ := a
  show _ ↔ (⟨a0, a1, a2⟩ : K3) = ⟨0, 0, 0⟩
  simp only [zero3, Bool.and_eq_true, eqG_iff, K3.mk.injEq, and_assoc]

/-! ## 4. The table and the check -/

/-- **An executable memory-side table**: nodes, generator, row values, `K3` coins and publics, and the
verifier-fixed columns (column index, required row values). -/
structure TabM (n : ℕ) where
  nodes : Fin n → ZMod p
  ω : ZMod p
  cols : ℕ → Fin n → ZMod p
  chals : ℕ → K3
  pubs : ℕ → K3
  prep : List (ℕ × (Fin n → ZMod p))

variable (Tm : ChipTemplate (ZMod p))

/-- The table data with the chip's (spec) gates. -/
noncomputable def TabM.toT {n : ℕ} (T : TabM n) : TableData (ZMod p) n :=
  ⟨Tm.width 3, T.nodes, T.ω, T.cols, Tm.allGates powerBasis3, slotE Tm.baseCols T.chals,
    slotE Tm.baseCols T.pubs, T.prep⟩

/-- The environment at row `i` (as `TableData.env`; computable). -/
def TabM.env {n : ℕ} (T : TabM n) (i : Fin n) : Env (ZMod p) where
  trace := fun j => if j < Tm.width 3 then T.cols j i else 0
  traceNext := fun j => if j < Tm.width 3 then
      (if h : (i : ℕ) + 1 < n then T.cols j ⟨i + 1, h⟩ else ∑ k, T.cols j k * lagW T.nodes (T.ω * T.nodes i) k)
    else 0
  chal := slotE Tm.baseCols T.chals
  pub := slotE Tm.baseCols T.pubs

theorem TabM.env_eq {n : ℕ} (T : TabM n) (i : Fin n) : (T.toT Tm).env i = T.env Tm i := rfl

/-- **The executable memory-chip check**: every source gate at every row; every fixed column. -/
def checkM {n : ℕ} (T : TabM n) : Bool :=
  (List.finRange n).all (fun i => (srcM Tm).all (srcOK Tm.baseCols (T.env Tm i))) &&
  T.prep.all (fun q => (List.finRange n).all fun i => decide (T.cols q.1 i = q.2 i))

theorem checkM_iff {n : ℕ} (T : TabM n) : checkM Tm T = true ↔ (T.toT Tm).checkTable = true := by
  have key : ((List.finRange n).all fun i => (srcM Tm).all (srcOK Tm.baseCols (T.env Tm i))) = true ↔
      ((T.toT Tm).gates.all fun g => (List.finRange n).all fun i => decide (g.eval ((T.toT Tm).env i) = 0)) =
        true := by
    constructor
    · intro h
      refine List.all_eq_true.mpr fun g hg => List.all_eq_true.mpr fun i _ => decide_eq_true ?_
      exact (rowOK_iff Tm (T.env Tm i)).mp (List.all_eq_true.mp h i (List.mem_finRange i)) g hg
    · intro h
      refine List.all_eq_true.mpr fun i _ => (rowOK_iff Tm (T.env Tm i)).mpr fun g hg => ?_
      exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp h g hg) i (List.mem_finRange i))
  unfold checkM TableData.checkTable
  rw [Bool.and_eq_true, Bool.and_eq_true, key]
  exact Iff.rfl

/-! ## 5. The finite characterisation, generic -/

section Generic
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]

/-- The constraint list of an `expandChip` is the reified expanded gate list. -/
theorem expandChip_C (T0 : ChipTemplate F) {e h : ℕ} (b : Module.Basis (Fin e) F K) (cv pv : ℕ → F)
    (orbit : StrictOrbitDomain F e h) (H : Finset F) :
    List.ofFn (expandChip T0 b cv pv orbit H).C =
      (T0.allGates b).map (coeffToMv (w := T0.width e) cv pv) := by
  show List.ofFn (fun i : Fin (T0.allGates b).length => coeffToMv cv pv ((T0.allGates b).get i)) = _
  exact ofFn_get_map _ _

end Generic

/-- **`chipM_iff`: an `expandChip` memory-side chip, finitely.**  If the RAP has the template's width, the
table's generator and row set, the expanded gates at the slot-encoded `K3` coins / publics, and the table's fixed
columns, then on injective, `ω`-adjacent nodes acceptance of the row interpolants is exactly `checkM`. -/
theorem chipM_iff {n : ℕ} (T : TabM n) (R : FixedPreprocessingRAP (ZMod p)) (P : Fin R.rap.w → (ZMod p)[X])
    (hinj : Function.Injective T.nodes)
    (hadj : ∀ i : Fin n, ∀ h : (i : ℕ) + 1 < n, T.nodes ⟨i + 1, h⟩ = T.ω * T.nodes i)
    (hw : R.rap.w = Tm.width 3) (hω : R.rap.ω = T.ω) (hH : R.rap.H = rowNodeSet T.nodes)
    (hC : List.ofFn R.rap.C = (Tm.allGates powerBasis3).map (coeffToMv (w := R.rap.w)
      (slotVal powerBasis3 Tm.baseCols fun i => K3.toK (T.chals i))
      (slotVal powerBasis3 Tm.baseCols fun i => K3.toK (T.pubs i))))
    (hprep : List.ofFn (fun j : Fin R.fixedCount =>
        (((R.preprocessingColumn j : Fin R.rap.w) : ℕ), R.preprocessing j)) =
      T.prep.map (fun q => (q.1, Lagrange.interpolate Finset.univ T.nodes q.2)))
    (hP : ∀ j : Fin R.rap.w, P j = Lagrange.interpolate Finset.univ T.nodes (fun i => T.cols j i)) :
    RAP.SatisfiesWithPreprocessing R P ↔ checkM Tm T = true := by
  rw [checkM_iff]
  refine satisfies_iff_checkTable (RingHom.id (ZMod p)) (T.toT Tm) R P hinj hadj hw hω hH ?_ ?_ hP
  · rw [hC]
    simp only [TabM.toT, List.map_map]
    refine List.map_congr_left fun g _ => ?_
    simp only [Function.comp_apply, mapC_id, RingHom.id_apply, slotE_eq]
  · exact hprep

/-! ## 6. Fixed-column helpers -/

/-- The root mask `i < kr` (walk chips). -/
def rootMaskE (n kr : ℕ) (i : Fin n) : ZMod p := if (i : ℕ) < kr then 1 else 0

/-- Masks `isFirst`, `isLast` at columns `0`, `1`. -/
def prep2 (n : ℕ) : List (ℕ × (Fin n → ZMod p)) := [(0, firstMaskE n), (1, lastMaskE n)]

/-- Masks `isFirst`, `isLast`, `isRoot` at columns `0`, `1`, `2`. -/
def prep3 (n kr : ℕ) : List (ℕ × (Fin n → ZMod p)) := [(0, firstMaskE n), (1, lastMaskE n), (2, rootMaskE n kr)]

theorem firstMask_interp {n : ℕ} (nodes : Fin n → ZMod p) :
    firstRowMask nodes = Lagrange.interpolate Finset.univ nodes (firstMaskE n) := rfl

theorem lastMask_interp {n : ℕ} (hn : 0 < n) (nodes : Fin n → ZMod p) :
    lastRowMask hn nodes = Lagrange.interpolate Finset.univ nodes (lastMaskE n) := by
  unfold lastRowMask
  congr 1; funext i
  simp only [lastMaskE, Fin.ext_iff]
  have := i.2
  by_cases h : (i : ℕ) + 1 = n
  · simp [h]; omega
  · simp [h]; omega

end Nock.V1J8.MemX
