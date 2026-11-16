/-
  Nock/V1J8/CompX.lean

  * `srcX`: the chip's gates as SOURCE gates (base `CoeffExpr`s, and `𝕂`-valued `MixedExpr`s at `col0Id`), with
    `gatesHX_src : gatesHX powerBasis3 deltaF = srcX.flatMap expandS` (the compiled coordinate gates are exactly the
    three coordinates of each source gate).  `srcOK_iff`: a source gate passes at a row iff each of its coordinate
    gates vanishes there (`mixedCompile_eval` at the power basis).
  * **`checkCompX`** (computable) and **`computeChipX_iff`**: for a table `T` (nodes injective and `ω`-adjacent,
    trace = the row interpolants), `SatisfiesWithPreprocessing (computeChipVCLHX …) P ↔ checkCompX T = true`.
-/
import Nock.V1J8.PubExe
import Nock.V1Check.Core

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Nock.V1J8.CompX

open Nock Nock.Reified Nock.Framework Nock.TraceGenExe Nock.Field Polynomial
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.T0Tower Nock.NockVMROM.Thm54.T0TowerFP
open Nock.NockVMROM.Thm54.VclL.Compute.TowerD (col0Id qGates)
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHX (baseGatesFX slotPairsX walkGatesFX gatesHX computeChipVCLHX)
open Nock.V1Check Nock.V1J8.Exe
open Nock.NockVMROM.Thm54.StrictExtension (StrictOrbitDomain)

/-! ## 1. `𝕂` rows over `K3`, and the source evaluator -/

/-- Three consecutive columns as a `K3`. -/
def readK (f : ℕ → ZMod p) (c : ℕ) : K3 := ⟨Gold.ofZ (f c), Gold.ofZ (f (c + 1)), Gold.ofZ (f (c + 2))⟩

/-- The `K3` environment of a base environment (`col0Id`: a `𝕂` value at column `c` occupies `c, c+1, c+2`). -/
def kenv (e : Env (ZMod p)) : Env K3 :=
  ⟨fun i => readK e.trace i, fun i => readK e.traceNext i, fun i => readK e.chal i, fun i => readK e.pub i⟩

noncomputable def mapEnvK (eK : Env K3) : Env KC :=
  ⟨fun i => K3.toK (eK.trace i), fun i => K3.toK (eK.traceNext i), fun i => K3.toK (eK.chal i),
    fun i => K3.toK (eK.pub i)⟩

theorem coord_readK (f : ℕ → ZMod p) (c : ℕ) (k : Fin 3) :
    coord powerBasis3 (K3.toK (readK f c)) k = f (c + (k : ℕ)) := by
  rw [coord_powerBasis3_toK]
  fin_cases k <;> simp [readK, Gold.toZ_ofZ]

theorem isCoordEnv_kenv (e : Env (ZMod p)) : IsCoordEnv powerBasis3 col0Id (mapEnvK (kenv e)) e where
  trace := fun idx k => (coord_readK e.trace idx k).symm
  traceNext := fun idx k => (coord_readK e.traceNext idx k).symm
  chal := fun idx k => (coord_readK e.chal idx k).symm
  pub := fun idx k => (coord_readK e.pub idx k).symm

def powK (a : K3) : ℕ → K3
  | 0 => 1
  | n + 1 => powK a n * a

theorem toK_powK (a : K3) : ∀ n, K3.toK (powK a n) = K3.toK a ^ n
  | 0 => by simp [powK, K3.toK_one]
  | n + 1 => by rw [powK, K3.toK_mul, toK_powK a n, pow_succ]

/-- **The executable evaluator of a source gate**: `𝕂` leaves read `K3`, base leaves read `ZMod p`. -/
def evalMZ (eK : Env K3) (eF : Env (ZMod p)) : MixedExpr (ZMod p) → K3
  | .Var .traceCur i => eK.trace i
  | .Var .traceNext i => eK.traceNext i
  | .Var .challenge i => eK.chal i
  | .Var .publicVal i => eK.pub i
  | .Lift g => g3 (Gold.ofZ (g.eval eF))
  | .Scale g u => K3.smul (Gold.ofZ (g.eval eF)) (evalMZ eK eF u)
  | .Const c => g3 (Gold.ofZ (c : ZMod p))
  | .Add x y => evalMZ eK eF x + evalMZ eK eF y
  | .Sub x y => evalMZ eK eF x - evalMZ eK eF y
  | .Neg x => - evalMZ eK eF x
  | .Mul x y => evalMZ eK eF x * evalMZ eK eF y
  | .Pow x n => powK (evalMZ eK eF x) n

theorem toK_evalMZ (eK : Env K3) (eF : Env (ZMod p)) (m : MixedExpr (ZMod p)) :
    K3.toK (evalMZ eK eF m) = m.eval (mapEnvK eK) eF := by
  induction m with
  | Var k i => cases k <;> rfl
  | Lift g => simp only [evalMZ, MixedExpr.eval, toK_g3, Gold.toZ_ofZ]
  | Scale g u ih => simp only [evalMZ, MixedExpr.eval, K3.toK_smul, Gold.toZ_ofZ, ih]
  | Const c => simp only [evalMZ, MixedExpr.eval, toK_g3, Gold.toZ_ofZ, map_intCast]
  | Add x y ihx ihy => simp only [evalMZ, MixedExpr.eval, K3.toK_add, ihx, ihy]
  | Sub x y ihx ihy => simp only [evalMZ, MixedExpr.eval, K3.toK_sub, ihx, ihy]
  | Neg x ihx => simp only [evalMZ, MixedExpr.eval, K3.toK_neg, ihx]
  | Mul x y ihx ihy => simp only [evalMZ, MixedExpr.eval, K3.toK_mul, ihx, ihy]
  | Pow x n ihx => simp only [evalMZ, MixedExpr.eval, toK_powK, ihx]

/-- **A compiled coordinate gate is the limb of the source value.** -/
theorem mix_eval (e : Env (ZMod p)) (m : MixedExpr (ZMod p)) (k : Fin 3) :
    (mixedCompile powerBasis3 col0Id m k).eval e =
      ![(evalMZ (kenv e) e m).c0.toZ, (evalMZ (kenv e) e m).c1.toZ, (evalMZ (kenv e) e m).c2.toZ] k := by
  rw [← mixedCompile_eval powerBasis3 col0Id (isCoordEnv_kenv e) m k, ← toK_evalMZ, coord_powerBasis3_toK]

/-- `v = 0`, limbwise. -/
def zero3 (v : K3) : Bool := eqG v.c0 0 && eqG v.c1 0 && eqG v.c2 0

theorem toZ_eq_zero (a : Gold) : a.toZ = 0 ↔ a = 0 :=
  ⟨fun h => Gold.toZ_injective (h.trans Gold.toZ_zero.symm), fun h => h ▸ Gold.toZ_zero⟩

theorem zero3_iff (v : K3) : zero3 v = true ↔ ∀ k : Fin 3, ![v.c0.toZ, v.c1.toZ, v.c2.toZ] k = 0 := by
  simp only [zero3, Bool.and_eq_true, eqG_iff, Fin.forall_fin_succ, Fin.forall_fin_zero_pi]
  simp [toZ_eq_zero, and_assoc]

/-! ## 2. Source gates -/

/-- A source gate: a base gate, or a `𝕂`-valued gate at `col0Id` (three coordinate gates). -/
inductive SG where
  | base : CoeffExpr (ZMod p) → SG
  | mix : MixedExpr (ZMod p) → SG

/-- The compiled coordinate gates of a source gate (at the power basis). -/
noncomputable def expandS : SG → List (CoeffExpr (ZMod p))
  | .base g => [g]
  | .mix m => List.ofFn (mixedCompile powerBasis3 col0Id m)

/-- **The compute chip's source gates**: base, the four `𝕂′` slot pairs (two `𝕂` gates each), the walk gates. -/
def srcX : List SG :=
  (baseGatesFX (F := ZMod p)).map SG.base ++
    (slotPairsX (ZMod p) deltaF).flatMap (fun q => [SG.mix q.1, SG.mix q.2]) ++
    (walkGatesFX (F := ZMod p)).map SG.mix

theorem base_part (A : List (CoeffExpr (ZMod p))) : (A.map SG.base).flatMap expandS = A := by
  induction A with
  | nil => rfl
  | cons g l ih => simp only [List.map_cons, List.flatMap_cons, ih]; rfl

theorem mid_part (B : List (Q (ZMod p))) :
    (B.flatMap fun q => [SG.mix q.1, SG.mix q.2]).flatMap expandS = B.flatMap (qGates powerBasis3) := by
  induction B with
  | nil => rfl
  | cons q l ih =>
      simp only [List.flatMap_cons, List.flatMap_append, ih]
      simp [expandS, qGates]

theorem walk_part (C : List (MixedExpr (ZMod p))) :
    (C.map SG.mix).flatMap expandS = C.flatMap fun g => List.ofFn (mixedCompile powerBasis3 col0Id g) := by
  induction C with
  | nil => rfl
  | cons g l ih => simp only [List.map_cons, List.flatMap_cons, ih]; rfl

/-- **The chip's gate list is the expansion of the source gates.** -/
theorem gatesHX_src : gatesHX powerBasis3 deltaF = srcX.flatMap expandS := by
  unfold gatesHX srcX
  rw [List.flatMap_append, List.flatMap_append, base_part, mid_part, walk_part]

/-- One source gate at one row. -/
def srcOK (e : Env (ZMod p)) : SG → Bool
  | .base g => decide (g.eval e = 0)
  | .mix m => zero3 (evalMZ (kenv e) e m)

theorem srcOK_iff (e : Env (ZMod p)) (s : SG) : srcOK e s = true ↔ ∀ g ∈ expandS s, g.eval e = 0 := by
  cases s with
  | base g => simp [srcOK, expandS]
  | mix m =>
      simp only [srcOK, expandS, List.forall_mem_ofFn_iff, mix_eval]
      exact zero3_iff _

theorem rowOK_iff (e : Env (ZMod p)) :
    srcX.all (srcOK e) = true ↔ ∀ g ∈ gatesHX powerBasis3 deltaF, g.eval e = 0 := by
  rw [gatesHX_src, List.all_eq_true]
  simp only [List.mem_flatMap]
  constructor
  · rintro h g ⟨s, hs, hg⟩
    exact (srcOK_iff e s).mp (h s hs) g hg
  · intro h s hs
    exact (srcOK_iff e s).mpr fun g hg => h g ⟨s, hs, hg⟩

/-! ## 3. The table and the check -/

/-- **An executable compute table** (`123` columns). -/
structure TabX (n : ℕ) where
  nodes : Fin n → ZMod p
  ω : ZMod p
  cols : ℕ → Fin n → ZMod p
  chal : ℕ → ZMod p
  pub : ℕ → ZMod p

def firstMaskE (n : ℕ) (i : Fin n) : ZMod p := if (i : ℕ) = 0 then 1 else 0
def lastMaskE (n : ℕ) (i : Fin n) : ZMod p := if (i : ℕ) + 1 = n then 1 else 0

/-- The table data with the chip's (spec) gates. -/
noncomputable def TabX.toT {n : ℕ} (T : TabX n) : TableData (ZMod p) n :=
  ⟨123, T.nodes, T.ω, T.cols, gatesHX powerBasis3 deltaF, T.chal, T.pub,
    [(17, firstMaskE n), (18, lastMaskE n)]⟩

/-- The environment at row `i` (as `TableData.env`; computable). -/
def TabX.env {n : ℕ} (T : TabX n) (i : Fin n) : Env (ZMod p) where
  trace := fun j => if j < 123 then T.cols j i else 0
  traceNext := fun j => if j < 123 then
      (if h : (i : ℕ) + 1 < n then T.cols j ⟨i + 1, h⟩ else ∑ k, T.cols j k * lagW T.nodes (T.ω * T.nodes i) k)
    else 0
  chal := T.chal
  pub := T.pub

theorem TabX.env_eq {n : ℕ} (T : TabX n) (i : Fin n) : T.toT.env i = T.env i := rfl

/-- **The executable compute-chip check**: every source gate at every row; the two mask columns. -/
def checkCompX {n : ℕ} (T : TabX n) : Bool :=
  (List.finRange n).all (fun i => srcX.all (srcOK (T.env i))) &&
  ([(17, firstMaskE n), (18, lastMaskE n)] : List (ℕ × (Fin n → ZMod p))).all
    (fun q => (List.finRange n).all fun i => decide (T.cols q.1 i = q.2 i))

theorem checkCompX_iff {n : ℕ} (T : TabX n) : checkCompX T = true ↔ T.toT.checkTable = true := by
  have key : ((List.finRange n).all fun i => srcX.all (srcOK (T.env i))) = true ↔
      (T.toT.gates.all fun g => (List.finRange n).all fun i => decide (g.eval (T.toT.env i) = 0)) = true := by
    constructor
    · intro h
      refine List.all_eq_true.mpr fun g hg => List.all_eq_true.mpr fun i _ => decide_eq_true ?_
      exact (rowOK_iff (T.env i)).mp (List.all_eq_true.mp h i (List.mem_finRange i)) g hg
    · intro h
      refine List.all_eq_true.mpr fun i _ => (rowOK_iff (T.env i)).mpr fun g hg => ?_
      exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp h g hg) i (List.mem_finRange i))
  unfold checkCompX TableData.checkTable
  rw [Bool.and_eq_true, Bool.and_eq_true, key]
  exact Iff.rfl

theorem ofFn_get_map {α β : Type} (gs : List α) (f : α → β) :
    List.ofFn (fun i : Fin gs.length => f (gs.get i)) = gs.map f := by
  apply List.ext_getElem <;> simp

theorem mapC_id (g : CoeffExpr (ZMod p)) : mapC (RingHom.id (ZMod p)) g = g := by
  induction g with
  | const c => rfl
  | var k i => rfl
  | add a b ha hb => simp [mapC, ha, hb]
  | sub a b ha hb => simp [mapC, ha, hb]
  | mul a b ha hb => simp [mapC, ha, hb]
  | neg a ha => simp [mapC, ha]
  | pow a n ha => simp [mapC, ha]

/-- **`computeChipX_iff`: the J-8 compute chip, finitely.**  For an executable table whose nodes are injective
and `ω`-adjacent, the chip at those nodes, coins and publics accepts the row interpolants iff `checkCompX`. -/
theorem computeChipX_iff {n h : ℕ} (T : TabX n) (hn : 0 < n) (orbit : StrictOrbitDomain (ZMod p) 3 h)
    (P : Fin (computeChipVCLHX hn T.nodes powerBasis3 deltaF T.chal T.pub orbit).rap.w → (ZMod p)[X])
    (hinj : Function.Injective T.nodes)
    (hadj : ∀ i : Fin n, ∀ h : (i : ℕ) + 1 < n, T.nodes ⟨i + 1, h⟩ = T.ω * T.nodes i)
    (hω : orbit.ω = T.ω)
    (hP : ∀ j, P j = Lagrange.interpolate Finset.univ T.nodes (fun i => T.cols j i)) :
    RAP.SatisfiesWithPreprocessing (computeChipVCLHX hn T.nodes powerBasis3 deltaF T.chal T.pub orbit) P ↔
      checkCompX T = true := by
  rw [checkCompX_iff]
  refine satisfies_iff_checkTable (RingHom.id (ZMod p)) T.toT _ P hinj hadj rfl hω rfl ?_ ?_ hP
  · show List.ofFn (fun i : Fin (gatesHX powerBasis3 deltaF).length =>
        coeffToMv T.chal T.pub ((gatesHX powerBasis3 deltaF).get i)) = _
    refine (ofFn_get_map (gatesHX powerBasis3 deltaF) _).trans ?_
    simp only [TabX.toT, List.map_map]
    refine List.map_congr_left fun g _ => ?_
    simp only [Function.comp_apply, mapC_id]
    rfl
  · simp only [List.ofFn_succ, List.ofFn_zero, computeChipVCLHX, FixedPreprocessingRAP.preprocessingColumn,
      RAP.preprocessingColumn, TabX.toT, List.map_cons, List.map_nil]
    refine congrArg₂ _ (Prod.ext rfl ?_) (congrArg₂ _ (Prod.ext rfl ?_) rfl)
    · show firstRowMask _ = _
      unfold firstRowMask
      congr 1
    · show lastRowMask hn _ = _
      unfold lastRowMask
      congr 1; funext i
      simp only [lastMaskE, Fin.ext_iff]
      have := i.2
      by_cases h : (i : ℕ) + 1 = n
      · simp [h]; omega
      · simp [h]; omega

end Nock.V1J8.CompX
