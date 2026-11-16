import Nock.NockVMROM.Thm54.VclL.Compute.ChipQ7
import Nock.NockVMROM.Thm54.P8Core.Batch1542Thm54T0TowerFP

/-!
# Route (d), phase 1 : the `(Re, Im)` translation of the compute chip's gates into `𝕂′`

Route (d) keeps the compute chip at `e = 3` over `𝕂` and reads a `𝕂′ = 𝕂(√δ)` value as a pair of
`𝕂` quantities: `Re` at the existing role (or coin slot) and `Im` at an APPENDED role (or a new coin
slot).  This module supplies, generically in `F`, `K`, `δ` and the Im map:

* `toQ` — the ONE translation `CorrectedFinalTypedExpr → Q F` into T0's pair language (`qmul` on
  products, literal on sums), and `toQW` on the width-309 language `WTyped`; compiled by the
  EXISTING `mixedCompile` at `col0 = id` (a `𝕂` quantity is named by its first physical limb);
* `towerEnv` — the `𝕂′` typed environment of an `(eK, eF)` pair: every `𝕂′` leaf is
  `Quad.mk (Re) (Im)` with `Im = 0` where the map has no entry;
* `toQ_val` / `toQ_isZero_iff` / `toQ_compiled_iff` — **the transport lemma**: the Re and Im
  compiled coordinate equations all vanish iff the gate holds in `𝕂′` at `towerEnv`;
* `appendOnly_iff` — for a `qLinear` gate (no product of two `𝕂′`-carrying factors) the EXISTING
  compiled gate is the Re twin, so committing only the Im twin is exact;
* `toQ_qdeg_le` / `towerTwin_degree_le_four` — no twin raises the degree; every Im twin of the
  compute chip's gates has degree `≤ 4`.
-/

namespace Nock.NockVMROM.Thm54
namespace VclL.Compute
namespace TowerD

open Nock Nock.Reified Module Polynomial
open Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler
open Nock.NockVMROM.Thm54.OptimizedComputeCorrectedFinal
open Nock.NockVMROM.Thm54.Unhosted309
open Nock.NockVMROM.Thm54.T0Tower Nock.NockVMROM.Thm54.T0TowerFP

set_option autoImplicit false
set_option maxRecDepth 300000

/-! ## 1. -/

section Basis
variable {F K : Type} [Field F] [Field K] [Algebra F K] (δ : K) [Fact (¬ IsSquare δ)]

/-- `{1, √δ}`: the power basis of `𝕂′ = 𝕂[X]/(X² − δ)` over `𝕂`, indexed by `Fin 2`. -/
noncomputable def quadBasis : Basis (Fin 2) K (Quad δ) :=
  (AdjoinRoot.powerBasis' (monic_X_pow_sub_C δ two_ne_zero)).basis.reindex
    (finCongr natDegree_X_pow_sub_C)

theorem quadBasis_apply (j : Fin 2) : quadBasis δ j = Quad.r δ ^ (j : ℕ) := by
  unfold quadBasis
  rw [Basis.reindex_apply, PowerBasis.basis_eq_pow]
  rfl

/-- `Fin 3 × Fin 2 ≃ Fin 6`, `(i, j) ↦ i + 3 j`: limbs `0..2` are Re, `3..5` are Im. -/
def e6 : Fin 3 × Fin 2 ≃ Fin 6 := (Equiv.prodComm (Fin 3) (Fin 2)).trans finProdFinEquiv

theorem e6_val (i : Fin 3) (j : Fin 2) : (e6 (i, j) : ℕ) = (i : ℕ) + 3 * (j : ℕ) := by
  simp [e6, finProdFinEquiv]

/-- **The tower basis**: `𝕂′` over `𝔽` with 6 limbs, Re limbs `b 0, b 1, b 2`, Im limbs
`b 0 • √δ, b 1 • √δ, b 2 • √δ` — built from the chip's own `Basis (Fin 3) F K`. -/
noncomputable def towerBasis (b : Basis (Fin 3) F K) : Basis (Fin 6) F (Quad δ) :=
  (b.smulTower (quadBasis δ)).reindex e6

theorem towerBasis_apply (b : Basis (Fin 3) F K) (i : Fin 3) (j : Fin 2) :
    towerBasis δ b (e6 (i, j)) = b i • Quad.r δ ^ (j : ℕ) := by
  simp [towerBasis, Basis.reindex_apply, Basis.smulTower_apply, quadBasis_apply]

/-- **The bridge** (V4T option B ⟷ T0 pairs): V4T's `limbVal` at `Kio := Quad δ`, `e := 6` over six
consecutive limbs is the `Quad.mk` of the two three-limb `𝕂` readings. -/
theorem limbVal_tower (b : Basis (Fin 3) F K) (f : ℕ → F) (base : ℕ) :
    LogUp.limbVal (towerBasis δ b) f base =
      Quad.mk δ (LogUp.limbVal b f base) (LogUp.limbVal b f (base + 3)) := by
  have hidx : ∀ i : Fin 3, base + ((i : ℕ) + 3) = base + 3 + (i : ℕ) := fun i => by omega
  unfold LogUp.limbVal
  rw [← Equiv.sum_comp e6, Fintype.sum_prod_type]
  simp only [Fin.sum_univ_two, towerBasis_apply, e6_val, Fin.val_zero, Fin.val_one, mul_zero,
    add_zero, mul_one, pow_zero, pow_one, hidx, Finset.sum_add_distrib]
  simp only [← smul_assoc, ← Finset.sum_smul]
  rw [Quad.mk, Algebra.smul_def, Algebra.smul_def, mul_one]

end Basis

/-! ## 2. The Im-role column map -/

/-- Where the Im half of each `𝕂′` leaf lives: the raw first limb of an appended `𝕂` role (trace
leaves; the current and the next row share the column), of a new coin slot (`3 · slot`), or of a
public.  `none` = the leaf is `𝕂`-valued (its Im is `0`). -/
structure ImMap where
  ext : Fin 63 → Option ℕ
  chal : Fin 12 → Option ℕ
  extPub : Fin 3 → Option ℕ
  walk : Fin 2 → Option ℕ

def fpRoleList : List ℕ := List.range 32 ++ (List.range 18).map (· + 36)

theorem fpRoleList_length : fpRoleList.length = 50 := by decide

/-- First column of the appended Im block: the current width of the VCL compute chip. -/
def imBase : ℕ := vclWidthE

/-- Rank of a fingerprint role in `fpRoleList`. -/
def fpRank (r : ℕ) : ℕ := if r < 32 then r else r - 4

/-- **The Im-role column map** of route (d): fingerprint role `r` has its Im triple at
`232 + 3·rank r` (`232.. 381`). -/
def fpImCol (r : Fin 63) : Option ℕ :=
  if (r : ℕ) < 32 ∨ (36 ≤ (r : ℕ) ∧ (r : ℕ) < 54) then some (imBase + 3 * fpRank r) else none

def towerChal (i : Fin 12) : Option ℕ :=
  if (i : ℕ) = 1 then some 36 else if (i : ℕ) = 5 then some 39
  else if (i : ℕ) = 7 then some 42 else if (i : ℕ) = 8 then some 45 else none

def fpImMap : ImMap := ⟨fpImCol, towerChal, fun _ => none, fun _ => none⟩

/-- Extend a map by one more `𝕂′` role (e.g. an inverse witness whose honest value is `𝕂′`). -/
def ImMap.addExt (M : ImMap) (r : Fin 63) (c : ℕ) : ImMap :=
  { M with ext := fun r' => if r' = r then some c else M.ext r' }

/-- Extend a map by an Im column for walk column `j`. -/
def ImMap.addWalk (M : ImMap) (j : Fin 2) (c : ℕ) : ImMap :=
  { M with walk := fun j' => if j' = j then some c else M.walk j' }

/-- Extend a map by an Im public for `𝕂` public `i`. -/
def ImMap.addPub (M : ImMap) (i : Fin 3) (c : ℕ) : ImMap :=
  { M with extPub := fun i' => if i' = i then some c else M.extPub i' }

/-- Beyond
`fpImMap`'s 50 fingerprint roles, every `𝕂` quantity that an honest trace must hold at a `𝕂′` value
gets an Im half, APPENDED after the fingerprint block (`382..`):
* role 56 (the inverse witness of gate 67, `e37·e56 = 1`) ↦ `382`;
* role 59 (the walk-acc residual witness, `w59 = walkAccStep309`, whose source reads the `𝕂′`
  label) ↦ `388`;
* walk column `W1` (the walk accumulator, additive against the `𝕂′` label in aux1 / ep4) ↦ `391`;
* `𝕂` public 1 (the walk seed, additive in ep4) ↦ public `48` (after V4T's `ρ` publics `42..47`).
Columns: `+150 + 12`; the Im block is `232.. 393`. -/
def fullImMap : ImMap :=
  ((((fpImMap.addExt 56 (imBase + 150)).addExt 57 (imBase + 153)).addExt 59 (imBase + 156)).addWalk
    1 (imBase + 159)).addPub 1 48

theorem fpImCol_isSome_iff (r : Fin 63) : (fpImCol r).isSome ↔ (r : ℕ) ∈ fpRoleList := by
  have := r.isLt
  unfold fpImCol fpRoleList
  constructor
  · intro h
    split_ifs at h with hr
    · simp only [List.mem_append, List.mem_range, List.mem_map]
      rcases hr with hr | hr
      · exact Or.inl hr
      · exact Or.inr ⟨(r : ℕ) - 36, by omega, by omega⟩
    · simp at h
  · intro h
    simp only [List.mem_append, List.mem_range, List.mem_map] at h
    rw [if_pos]
    · rfl
    · rcases h with h | ⟨a, ha, hra⟩
      · exact Or.inl h
      · exact Or.inr ⟨by omega, by omega⟩

/-- **Append-only**: every Im triple sits at or after the current width `232`, so no existing
column constant moves. -/
theorem fpImCol_ge_width (r : Fin 63) (c : ℕ) (h : fpImCol r = some c) : vclWidthE ≤ c := by
  unfold fpImCol imBase at h
  split_ifs at h
  · cases h; omega

/-- The Im block ends at `232 + 150 = 382`. -/
theorem fpImCol_lt (r : Fin 63) (c : ℕ) (h : fpImCol r = some c) : c + 3 ≤ vclWidthE + 150 := by
  unfold fpImCol imBase fpRank at h
  split_ifs at h with h1 h2
  · cases h; omega
  · cases h; omega

/-- The appended triples of distinct roles are disjoint. -/
theorem fpImCol_disjoint (r r' : Fin 63) (c c' : ℕ) (h : fpImCol r = some c)
    (h' : fpImCol r' = some c') (hne : r ≠ r') : c + 3 ≤ c' ∨ c' + 3 ≤ c := by
  have hne' : (r : ℕ) ≠ (r' : ℕ) := fun he => hne (Fin.ext he)
  unfold fpImCol imBase fpRank at h h'
  split_ifs at h h' with h1 h2 h3 h4 h5 h6 <;> (cases h; cases h') <;> omega

/-- The `𝕂′` coin Im slots are new (`≥ 12`), and the IO pair reads limbs `42..44` / `45..47`. -/
theorem towerChal_new (i : Fin 12) (c : ℕ) (h : towerChal i = some c) : 36 ≤ c := by
  unfold towerChal at h
  split_ifs at h <;> (cases h; omega)

/-! ## 3. The pair language: leaves and powers -/

section Pair
variable (F : Type)

def qneg (a : Q F) : Q F := (.Neg a.1, .Neg a.2)

def qpow (δ : F) (a : Q F) : ℕ → Q F
  | 0 => (.Const 1, .Const 0)
  | n + 1 => qmul F δ a (qpow δ a n)

/-- A base-field leaf (`Im = 0`). -/
def qlift (g : CoeffExpr F) : Q F := (.Lift g, .Const 0)

def qconst (c : ℤ) : Q F := (.Const c, .Const 0)

/-- A `𝕂` quantity named by its first physical limb `re`, with its Im at `im` (if any). -/
def qvar (kind : VarKind) (re : ℕ) : Option ℕ → Q F
  | none => (.Var kind re, .Const 0)
  | some c => (.Var kind re, .Var kind c)

/-- **The translation** of a corrected typed gate into its `(Re, Im)` pair over `𝕂`-roles.
`n` is the Form R exponent `MemoryTable.pwScaleExp` (only `lamPow` reads it). -/
def toQ (M : ImMap) (n : ℕ) (δ : F) : CorrectedFinalTypedExpr → Q F
  | .baseCur i => qlift F (.var .traceCur i)
  | .baseNext i => qlift F (.var .traceNext i)
  | .extCur i => qvar F .traceCur (13 + 3 * (i : ℕ)) (M.ext i)
  | .extNext i => qvar F .traceNext (13 + 3 * (i : ℕ)) (M.ext i)
  | .challenge i => qvar F .challenge (3 * (i : ℕ)) (M.chal i)
  | .extensionPublic i => qvar F .publicVal (3 * (i : ℕ)) (M.extPub i)
  | .scalarPublic i => qlift F (.var .publicVal (20 + (i : ℕ)))
  | .const c => qconst F c
  | .add x y => qadd F (toQ M n δ x) (toQ M n δ y)
  | .sub x y => qsub F (toQ M n δ x) (toQ M n δ y)
  | .mul x y => qmul F δ (toQ M n δ x) (toQ M n δ y)
  | .neg x => qneg F (toQ M n δ x)
  | .pow x m => qpow F δ (toQ M n δ x) m
  | .certBase i => qlift F (.var .traceCur (202 + (i : ℕ)))
  | .certExt i => qvar F .traceCur (296 + 3 * (i : ℕ)) none
  | .lamPow d => if (d : ℕ) ≤ n then qpow F δ (qvar F .challenge (3 * 9) (M.chal 9)) (n - d)
      else qconst F 0
  | .expCur => qlift F (.var .traceCur 302)

/-- The translation on the width-309 language (`W0`/`W1` named by their first limbs `303`/`306`). -/
def toQW (M : ImMap) (n : ℕ) (δ : F) : WTyped → Q F
  | .leaf t => toQ F M n δ t
  | .wCur j => qvar F .traceCur (303 + 3 * (j : ℕ)) (M.walk j)
  | .wNext j => qvar F .traceNext (303 + 3 * (j : ℕ)) (M.walk j)
  | .add x y => qadd F (toQW M n δ x) (toQW M n δ y)
  | .sub x y => qsub F (toQW M n δ x) (toQW M n δ y)
  | .mul x y => qmul F δ (toQW M n δ x) (toQW M n δ y)
  | .neg x => qneg F (toQW M n δ x)
  | .pow x m => qpow F δ (toQW M n δ x) m

/-- The identity limb map: a `MixedExpr` variable names its first physical limb. -/
def col0Id : VarKind → ℕ → ℕ := fun _ i => i

end Pair

/-! ## 4. Degree: no twin raises the degree -/

section Degree
variable (F : Type)

theorem qdeg_qadd (a b : Q F) : qdeg F (qadd F a b) ≤ max (qdeg F a) (qdeg F b) := by
  simp only [qdeg, qadd, MixedExpr.degree]; omega

theorem qdeg_qsub (a b : Q F) : qdeg F (qsub F a b) ≤ max (qdeg F a) (qdeg F b) := by
  simp only [qdeg, qsub, MixedExpr.degree]; omega

theorem qdeg_qmul (δ : F) (a b : Q F) : qdeg F (qmul F δ a b) ≤ qdeg F a + qdeg F b := by
  simp only [qdeg, qmul, MixedExpr.degree, CoeffExpr.degree]; omega

theorem qdeg_qneg (a : Q F) : qdeg F (qneg F a) = qdeg F a := by
  simp only [qdeg, qneg, MixedExpr.degree]

theorem qdeg_qpow (δ : F) (a : Q F) (n : ℕ) : qdeg F (qpow F δ a n) ≤ n * qdeg F a := by
  induction n with
  | zero => simp [qpow, qdeg, MixedExpr.degree]
  | succ n ih =>
      refine (qdeg_qmul F δ a _).trans ?_
      rw [Nat.succ_mul]; omega

theorem qdeg_qvar (kind : VarKind) (re : ℕ) (im : Option ℕ) :
    qdeg F (qvar F kind re im) = (MixedExpr.Var kind re : MixedExpr F).degree := by
  cases im <;> cases kind <;> simp [qvar, qdeg, MixedExpr.degree]

/-- **The translation never raises the degree.** -/
theorem toQ_qdeg_le (M : ImMap) (n : ℕ) (δ : F) :
    ∀ g : CorrectedFinalTypedExpr, qdeg F (toQ F M n δ g) ≤ g.degree
  | .baseCur i => by simp [toQ, qlift, qdeg, MixedExpr.degree, CoeffExpr.degree,
      CorrectedFinalTypedExpr.degree]
  | .baseNext i => by simp [toQ, qlift, qdeg, MixedExpr.degree, CoeffExpr.degree,
      CorrectedFinalTypedExpr.degree]
  | .extCur i => by rw [toQ, qdeg_qvar]; simp [MixedExpr.degree, CorrectedFinalTypedExpr.degree]
  | .extNext i => by rw [toQ, qdeg_qvar]; simp [MixedExpr.degree, CorrectedFinalTypedExpr.degree]
  | .challenge i => by rw [toQ, qdeg_qvar]; simp [MixedExpr.degree, CorrectedFinalTypedExpr.degree]
  | .extensionPublic i => by
      rw [toQ, qdeg_qvar]; simp [MixedExpr.degree, CorrectedFinalTypedExpr.degree]
  | .scalarPublic i => by simp [toQ, qlift, qdeg, MixedExpr.degree, CoeffExpr.degree,
      CorrectedFinalTypedExpr.degree]
  | .const c => by simp [toQ, qconst, qdeg, MixedExpr.degree, CorrectedFinalTypedExpr.degree]
  | .add x y => by
      refine (qdeg_qadd F _ _).trans ?_
      have := toQ_qdeg_le M n δ x; have := toQ_qdeg_le M n δ y
      simp only [CorrectedFinalTypedExpr.degree]; omega
  | .sub x y => by
      refine (qdeg_qsub F _ _).trans ?_
      have := toQ_qdeg_le M n δ x; have := toQ_qdeg_le M n δ y
      simp only [CorrectedFinalTypedExpr.degree]; omega
  | .mul x y => by
      refine (qdeg_qmul F δ _ _).trans ?_
      have := toQ_qdeg_le M n δ x; have := toQ_qdeg_le M n δ y
      simp only [CorrectedFinalTypedExpr.degree]; omega
  | .neg x => by
      rw [toQ, qdeg_qneg]; simpa [CorrectedFinalTypedExpr.degree] using toQ_qdeg_le M n δ x
  | .pow x m => by
      refine (qdeg_qpow F δ _ m).trans ?_
      simp only [CorrectedFinalTypedExpr.degree]
      exact Nat.mul_le_mul_left m (toQ_qdeg_le M n δ x)
  | .certBase i => by simp [toQ, qlift, qdeg, MixedExpr.degree, CoeffExpr.degree,
      CorrectedFinalTypedExpr.degree]
  | .certExt i => by rw [toQ, qdeg_qvar]; simp [MixedExpr.degree, CorrectedFinalTypedExpr.degree]
  | .lamPow d => by
      simp only [toQ, CorrectedFinalTypedExpr.degree]
      split_ifs
      · refine (qdeg_qpow F δ _ _).trans ?_
        rw [qdeg_qvar]; simp [MixedExpr.degree]
      · simp [qconst, qdeg, MixedExpr.degree]
  | .expCur => by simp [toQ, qlift, qdeg, MixedExpr.degree, CoeffExpr.degree,
      CorrectedFinalTypedExpr.degree]

theorem toQW_qdeg_le (M : ImMap) (n : ℕ) (δ : F) :
    ∀ g : WTyped, qdeg F (toQW F M n δ g) ≤ g.degree
  | .leaf t => toQ_qdeg_le F M n δ t
  | .wCur j => by rw [toQW, qdeg_qvar]; simp [MixedExpr.degree, WTyped.degree]
  | .wNext j => by rw [toQW, qdeg_qvar]; simp [MixedExpr.degree, WTyped.degree]
  | .add x y => by
      refine (qdeg_qadd F _ _).trans ?_
      have := toQW_qdeg_le M n δ x; have := toQW_qdeg_le M n δ y
      simp only [WTyped.degree]; omega
  | .sub x y => by
      refine (qdeg_qsub F _ _).trans ?_
      have := toQW_qdeg_le M n δ x; have := toQW_qdeg_le M n δ y
      simp only [WTyped.degree]; omega
  | .mul x y => by
      refine (qdeg_qmul F δ _ _).trans ?_
      have := toQW_qdeg_le M n δ x; have := toQW_qdeg_le M n δ y
      simp only [WTyped.degree]; omega
  | .neg x => by rw [toQW, qdeg_qneg]; simpa [WTyped.degree] using toQW_qdeg_le M n δ x
  | .pow x m => by
      refine (qdeg_qpow F δ _ m).trans ?_
      simp only [WTyped.degree]
      exact Nat.mul_le_mul_left m (toQW_qdeg_le M n δ x)

/-- **Degree `≤ 4` of every twin** of the compute chip's typed gates: the 82 core gates, the six
degree-2 and the degree-4 endpoint (`corrected_lowered_degrees`), and the width-309 endpoint
lists (`endpoint2_309_degree`, `endpoint4_309_degree`), Re and Im, for every Im map, after
compilation at any basis. -/
theorem towerTwin_degree_le_four [Field F] {K : Type} [Field K] [Algebra F K] {e : ℕ}
    (b : Basis (Fin e) F K) (M : ImMap) (n : ℕ) (δ : F) :
    (∀ g ∈ correctedLoweredExt ++ correctedEndpoint2 ++ correctedEndpoint4, ∀ k : Fin e,
      (mixedCompile b col0Id (toQ F M n δ g).1 k).degree ≤ 4 ∧
        (mixedCompile b col0Id (toQ F M n δ g).2 k).degree ≤ 4) ∧
    (∀ g ∈ endpoint2_309 ++ endpoint4_309, ∀ k : Fin e,
      (mixedCompile b col0Id (toQW F M n δ g).1 k).degree ≤ 4 ∧
        (mixedCompile b col0Id (toQW F M n δ g).2 k).degree ≤ 4) := by
  obtain ⟨h1, h2, h3⟩ := corrected_lowered_degrees
  refine ⟨fun g hg k => ?_, fun g hg k => ?_⟩
  · have hd : g.degree ≤ 4 := by
      simp only [List.mem_append] at hg
      rcases hg with (hg | hg) | hg
      · exact h1 g hg
      · exact (h2 g hg).trans (by norm_num)
      · exact h3 g hg
    have hc := gate_compiled_degree_le b col0Id (toQ F M n δ g) k
    have hq := toQ_qdeg_le F M n δ g
    exact ⟨hc.1.trans (hq.trans hd), hc.2.trans (hq.trans hd)⟩
  · have hd : g.degree ≤ 4 := by
      simp only [List.mem_append] at hg
      rcases hg with hg | hg
      · exact (endpoint2_309_degree g hg).trans (by norm_num)
      · exact endpoint4_309_degree g hg
    have hc := gate_compiled_degree_le b col0Id (toQW F M n δ g) k
    have hq := toQW_qdeg_le F M n δ g
    exact ⟨hc.1.trans (hq.trans hd), hc.2.trans (hq.trans hd)⟩

end Degree

/-! ## 5. Semantics: the tower environment and the transport lemma -/

section Semantics
variable {F K : Type} [Field F] [Field K] [Algebra F K]

/-- The `𝕂` value of an Im slot (`0` where the map has none). -/
def imVal (f : ℕ → K) : Option ℕ → K
  | none => 0
  | some c => f c

/-- The `𝕂` reading of a variable kind. -/
def kread (eK : Env K) : VarKind → ℕ → K
  | .traceCur => eK.trace
  | .traceNext => eK.traceNext
  | .challenge => eK.chal
  | .publicVal => eK.pub

/-- **The `𝕂′` typed environment** of an `(eK, eF)` pair under the Im map `M`: a `𝕂′` leaf is
`Quad.mk (Re) (Im)` with Re at its existing role / slot and Im at the map's (or `0`). -/
noncomputable def towerEnv (δ : F) (M : ImMap) (eK : Env K) (eF : Env F) :
    CorrectedFinalTypedEnv F (Quad (algebraMap F K δ)) where
  baseTrace i := eF.trace i
  baseTraceNext i := eF.traceNext i
  extTrace i := Quad.mk _ (eK.trace (13 + 3 * (i : ℕ))) (imVal eK.trace (M.ext i))
  extTraceNext i := Quad.mk _ (eK.traceNext (13 + 3 * (i : ℕ))) (imVal eK.traceNext (M.ext i))
  chal i := Quad.mk _ (eK.chal (3 * (i : ℕ))) (imVal eK.chal (M.chal i))
  extensionPublic i := Quad.mk _ (eK.pub (3 * (i : ℕ))) (imVal eK.pub (M.extPub i))
  scalarPublic i := eF.pub (20 + (i : ℕ))
  certBase i := eF.trace (202 + (i : ℕ))
  certExt i := Quad.mk _ (eK.trace (296 + 3 * (i : ℕ))) 0
  expCol := eF.trace 302

/-- The width-309 tower environment (walk columns `W0`/`W1` as pairs). -/
noncomputable def towerEnv309 (δ : F) (M : ImMap) (eK : Env K) (eF : Env F) :
    Env309 F (Quad (algebraMap F K δ)) where
  base := towerEnv δ M eK eF
  walk j := Quad.mk _ (eK.trace (303 + 3 * (j : ℕ))) (imVal eK.trace (M.walk j))
  walkNext j := Quad.mk _ (eK.traceNext (303 + 3 * (j : ℕ))) (imVal eK.traceNext (M.walk j))

theorem mixed_var_eval (eK : Env K) (eF : Env F) (kind : VarKind) (i : ℕ) :
    (MixedExpr.Var kind i : MixedExpr F).eval eK eF = kread eK kind i := by
  cases kind <;> rfl

theorem qvar_val (δ : F) (eK : Env K) (eF : Env F) (kind : VarKind) (re : ℕ) (im : Option ℕ) :
    Q.val δ (qvar F kind re im) eK eF = Quad.mk _ (kread eK kind re) (imVal (kread eK kind) im) := by
  cases im <;> cases kind <;> simp [qvar, Q.val, MixedExpr.eval, kread, imVal]

theorem Quad.mk_neg' (d a b : K) : Quad.mk d (-a) (-b) = -Quad.mk d a b := by
  simp only [Quad.mk, map_neg]; ring

theorem qneg_val (δ : F) (eK : Env K) (eF : Env F) (a : Q F) :
    Q.val δ (qneg F a) eK eF = -Q.val δ a eK eF := by
  simp only [Q.val, qneg, MixedExpr.eval, Quad.mk_neg']

theorem qpow_val (δ : F) (eK : Env K) (eF : Env F) (a : Q F) (n : ℕ) :
    Q.val δ (qpow F δ a n) eK eF = Q.val δ a eK eF ^ n := by
  induction n with
  | zero => simp [qpow, Q.val, MixedExpr.eval, Quad.mk]
  | succ n ih => rw [qpow, qmul_val, ih]; exact (pow_succ' _ _).symm

theorem qlift_val (δ : F) (eK : Env K) (eF : Env F) (g : CoeffExpr F) :
    Q.val δ (qlift F g) eK eF = algebraMap F (Quad (algebraMap F K δ)) (g.eval eF) := by
  show Quad.mk _ (algebraMap F K (g.eval eF)) ((0 : ℤ) : K) = _
  rw [Int.cast_zero, Quad.mk_base]
  exact (IsScalarTower.algebraMap_apply F K _ _).symm

theorem qconst_val (δ : F) (eK : Env K) (eF : Env F) (c : ℤ) :
    Q.val δ (qconst F c) eK eF = (c : Quad (algebraMap F K δ)) := by
  show Quad.mk _ ((c : ℤ) : K) ((0 : ℤ) : K) = _
  rw [Int.cast_zero, Quad.mk_base, map_intCast]

theorem ringChar_quad (d : K) [Fact (¬ IsSquare d)] : ringChar (Quad d) = ringChar K :=
  (Algebra.ringChar_eq K (Quad d)).symm

theorem pwScaleExp_quad (d : K) [Fact (¬ IsSquare d)] :
    MemoryTable.pwScaleExp (Quad d) = MemoryTable.pwScaleExp K := by
  simp [MemoryTable.pwScaleExp, ringChar_quad]

variable (δ : F) [Fact (¬ IsSquare (algebraMap F K δ))]

/-- **The value of the translation is the `𝕂′` gate at the tower environment.** -/
theorem toQ_val (M : ImMap) (n : ℕ) (hn : n = MemoryTable.pwScaleExp K) (eK : Env K) (eF : Env F) :
    ∀ g : CorrectedFinalTypedExpr,
      Q.val δ (toQ F M n δ g) eK eF = g.eval (towerEnv δ M eK eF)
  | .baseCur i => by rw [toQ, qlift_val]; rfl
  | .baseNext i => by rw [toQ, qlift_val]; rfl
  | .extCur i => by rw [toQ, qvar_val]; rfl
  | .extNext i => by rw [toQ, qvar_val]; rfl
  | .challenge i => by rw [toQ, qvar_val]; rfl
  | .extensionPublic i => by rw [toQ, qvar_val]; rfl
  | .scalarPublic i => by rw [toQ, qlift_val]; rfl
  | .const c => by rw [toQ, qconst_val]; rfl
  | .add x y => by
      rw [toQ, qadd_val, toQ_val M n hn eK eF x, toQ_val M n hn eK eF y]; rfl
  | .sub x y => by
      rw [toQ, qsub_val, toQ_val M n hn eK eF x, toQ_val M n hn eK eF y]; rfl
  | .mul x y => by
      rw [toQ, qmul_val, toQ_val M n hn eK eF x, toQ_val M n hn eK eF y]; rfl
  | .neg x => by rw [toQ, qneg_val, toQ_val M n hn eK eF x]; rfl
  | .pow x m => by rw [toQ, qpow_val, toQ_val M n hn eK eF x]; rfl
  | .certBase i => by rw [toQ, qlift_val]; rfl
  | .certExt i => by rw [toQ, qvar_val]; rfl
  | .lamPow d => by
      have hq : n = MemoryTable.pwScaleExp (Quad (algebraMap F K δ)) := by
        rw [pwScaleExp_quad, hn]
      simp only [toQ, CorrectedFinalTypedExpr.eval, lamPowVal]
      rw [← hq]
      split_ifs
      · rw [qpow_val, qvar_val]; rfl
      · rw [qconst_val]; simp
  | .expCur => by rw [toQ, qlift_val]; rfl

theorem toQW_val (M : ImMap) (n : ℕ) (hn : n = MemoryTable.pwScaleExp K) (eK : Env K) (eF : Env F) :
    ∀ g : WTyped, Q.val δ (toQW F M n δ g) eK eF = g.eval (towerEnv309 δ M eK eF)
  | .leaf t => toQ_val δ M n hn eK eF t
  | .wCur j => by rw [toQW, qvar_val]; rfl
  | .wNext j => by rw [toQW, qvar_val]; rfl
  | .add x y => by
      rw [toQW, qadd_val, toQW_val M n hn eK eF x, toQW_val M n hn eK eF y]; rfl
  | .sub x y => by
      rw [toQW, qsub_val, toQW_val M n hn eK eF x, toQW_val M n hn eK eF y]; rfl
  | .mul x y => by
      rw [toQW, qmul_val, toQW_val M n hn eK eF x, toQW_val M n hn eK eF y]; rfl
  | .neg x => by rw [toQW, qneg_val, toQW_val M n hn eK eF x]; rfl
  | .pow x m => by rw [toQW, qpow_val, toQW_val M n hn eK eF x]; rfl

/-- **The transport lemma**: the Re and Im equations both hold iff the gate holds in `𝕂′` at
`Quad.mk Re Im`. -/
theorem toQ_isZero_iff (M : ImMap) (n : ℕ) (hn : n = MemoryTable.pwScaleExp K) (eK : Env K)
    (eF : Env F) (g : CorrectedFinalTypedExpr) :
    Q.IsZero (toQ F M n δ g) eK eF ↔ g.eval (towerEnv δ M eK eF) = 0 := by
  rw [Q.isZero_iff δ eK eF, toQ_val δ M n hn eK eF g]

theorem toQW_isZero_iff (M : ImMap) (n : ℕ) (hn : n = MemoryTable.pwScaleExp K) (eK : Env K)
    (eF : Env F) (g : WTyped) :
    Q.IsZero (toQW F M n δ g) eK eF ↔ g.eval (towerEnv309 δ M eK eF) = 0 := by
  rw [Q.isZero_iff δ eK eF, toQW_val δ M n hn eK eF g]

/-- **The transport lemma, compiled** (the existing `mixedCompile` at finrank `e`, `col0 = id`):
all `2e` base-field coordinate equations of the twin pair vanish iff the gate holds in `𝕂′`. -/
theorem toQ_compiled_iff [FiniteDimensional F K] {e : ℕ} (b : Basis (Fin e) F K)
    (M : ImMap) (n : ℕ) (hn : n = MemoryTable.pwScaleExp K) {eK : Env K} {eF : Env F}
    (h : IsCoordEnv b col0Id eK eF) (g : CorrectedFinalTypedExpr) :
    ((∀ k, (mixedCompile b col0Id (toQ F M n δ g).1 k).eval eF = 0) ∧
        ∀ k, (mixedCompile b col0Id (toQ F M n δ g).2 k).eval eF = 0) ↔
      g.eval (towerEnv δ M eK eF) = 0 :=
  (gate_zero_iff_compiled b col0Id h _).symm.trans (toQ_isZero_iff δ M n hn eK eF g)

theorem toQW_compiled_iff [FiniteDimensional F K] {e : ℕ} (b : Basis (Fin e) F K)
    (M : ImMap) (n : ℕ) (hn : n = MemoryTable.pwScaleExp K) {eK : Env K} {eF : Env F}
    (h : IsCoordEnv b col0Id eK eF) (g : WTyped) :
    ((∀ k, (mixedCompile b col0Id (toQW F M n δ g).1 k).eval eF = 0) ∧
        ∀ k, (mixedCompile b col0Id (toQW F M n δ g).2 k).eval eF = 0) ↔
      g.eval (towerEnv309 δ M eK eF) = 0 :=
  (gate_zero_iff_compiled b col0Id h _).symm.trans (toQW_isZero_iff δ M n hn eK eF g)

end Semantics

/-! ## 6. The pair gather: every raw trace has its `𝕂` window reading -/

section Gather
variable {F K : Type} [Field F] [Field K] [Algebra F K]

/-- The `𝕂` reading of three consecutive raw limbs starting at each index (`LogUp.limbVal`). -/
noncomputable def gatherEnv (b : Basis (Fin 3) F K) (eF : Env F) : Env K where
  trace := LogUp.limbVal b eF.trace
  traceNext := LogUp.limbVal b eF.traceNext
  chal := LogUp.limbVal b eF.chal
  pub := LogUp.limbVal b eF.pub

theorem isCoordEnv_gather (b : Basis (Fin 3) F K) (eF : Env F) :
    IsCoordEnv b col0Id (gatherEnv b eF) eF where
  trace i k := (LogUp.coord_limbVal b eF.trace i k).symm
  traceNext i k := (LogUp.coord_limbVal b eF.traceNext i k).symm
  chal i k := (LogUp.coord_limbVal b eF.chal i k).symm
  pub i k := (LogUp.coord_limbVal b eF.pub i k).symm

end Gather

/-! ## 7. Linear gates: the existing compiled gate IS the Re twin (append-only)

A gate is `qLinear` when no product (or power `≥ 2`) has a `𝕂′`-carrying factor on both sides.
For such a gate the Re half of the `𝕂′` value is the gate evaluated at the Re readings, so the
chip's existing compiled gate (`correctedFinalTypedCompile`) is the Re twin and only the Im twin is
appended.  A gate that is not `qLinear` needs its Re body REPLACED by `(toQ g).1` (the `δ·Im·Im`
term of `qmul`). -/

/-- Does the translated gate carry an Im half (reads a leaf the map sends to `some`)? -/
def hasIm (M : ImMap) : CorrectedFinalTypedExpr → Bool
  | .extCur i => (M.ext i).isSome
  | .extNext i => (M.ext i).isSome
  | .challenge i => (M.chal i).isSome
  | .extensionPublic i => (M.extPub i).isSome
  | .lamPow _ => (M.chal 9).isSome
  | .add x y => hasIm M x || hasIm M y
  | .sub x y => hasIm M x || hasIm M y
  | .mul x y => hasIm M x || hasIm M y
  | .neg x => hasIm M x
  | .pow x _ => hasIm M x
  | _ => false

/-- No product of two `𝕂′`-carrying factors. -/
def qLinear (M : ImMap) : CorrectedFinalTypedExpr → Bool
  | .add x y => qLinear M x && qLinear M y
  | .sub x y => qLinear M x && qLinear M y
  | .mul x y => (!hasIm M x && qLinear M y) || (qLinear M x && !hasIm M y)
  | .neg x => qLinear M x
  | .pow x m => !hasIm M x || (decide (m ≤ 1) && qLinear M x)
  | .lamPow _ => (M.chal 9).isNone
  | _ => true

/-- `hasIm` on the width-309 language. -/
def hasImW (M : ImMap) : WTyped → Bool
  | .leaf t => hasIm M t
  | .wCur j => (M.walk j).isSome
  | .wNext j => (M.walk j).isSome
  | .add x y => hasImW M x || hasImW M y
  | .sub x y => hasImW M x || hasImW M y
  | .mul x y => hasImW M x || hasImW M y
  | .neg x => hasImW M x
  | .pow x _ => hasImW M x

/-- `qLinear` on the width-309 language. -/
def qLinearW (M : ImMap) : WTyped → Bool
  | .leaf t => qLinear M t
  | .add x y => qLinearW M x && qLinearW M y
  | .sub x y => qLinearW M x && qLinearW M y
  | .mul x y => (!hasImW M x && qLinearW M y) || (qLinearW M x && !hasImW M y)
  | .neg x => qLinearW M x
  | .pow x m => !hasImW M x || (decide (m ≤ 1) && qLinearW M x)
  | _ => true

section Linear
variable {F K : Type} [Field F] [Field K] [Algebra F K]

/-- The pre-tower (`𝕂`) typed environment read off the same `(eK, eF)`: the Re readings. -/
def reEnv (eK : Env K) (eF : Env F) : CorrectedFinalTypedEnv F K where
  baseTrace i := eF.trace i
  baseTraceNext i := eF.traceNext i
  extTrace i := eK.trace (13 + 3 * (i : ℕ))
  extTraceNext i := eK.traceNext (13 + 3 * (i : ℕ))
  chal i := eK.chal (3 * (i : ℕ))
  extensionPublic i := eK.pub (3 * (i : ℕ))
  scalarPublic i := eF.pub (20 + (i : ℕ))
  certBase i := eF.trace (202 + (i : ℕ))
  certExt i := eK.trace (296 + 3 * (i : ℕ))
  expCol := eF.trace 302

/-- **The bridge to the chip's existing coordinate relation**: the pair gather's Re readings are a
coordinate environment of the corrected compiler. -/
theorem isCorrectedFinalCoordEnv_reEnv (b : Basis (Fin 3) F K) {eK : Env K} {eF : Env F}
    (h : IsCoordEnv b col0Id eK eF) : IsCorrectedFinalCoordEnv b (reEnv eK eF) eF where
  baseTrace _ := rfl
  baseTraceNext _ := rfl
  extTrace i k := h.trace (13 + 3 * (i : ℕ)) k
  extTraceNext i k := h.traceNext (13 + 3 * (i : ℕ)) k
  chal i k := h.chal (3 * (i : ℕ)) k
  extensionPublic i k := h.pub (3 * (i : ℕ)) k
  scalarPublic _ := rfl
  certBase _ := rfl
  certExt i k := h.trace (296 + 3 * (i : ℕ)) k
  expCol := rfl

variable (δ : F)

theorem qvar_fst_eval (eK : Env K) (eF : Env F) (kind : VarKind) (re : ℕ) (im : Option ℕ) :
    (qvar F kind re im).1.eval eK eF = kread eK kind re := by
  cases im <;> simp [qvar, mixed_var_eval]

theorem qvar_snd_eval_none (eK : Env K) (eF : Env F) (kind : VarKind) (re : ℕ) :
    (qvar F kind re none).2.eval eK eF = 0 := by
  simp [qvar, MixedExpr.eval]

theorem qpow_eval_of_im_zero (eK : Env K) (eF : Env F) (a : Q F) (ha : a.2.eval eK eF = 0) (m : ℕ) :
    (qpow F δ a m).1.eval eK eF = a.1.eval eK eF ^ m ∧ (qpow F δ a m).2.eval eK eF = 0 := by
  induction m with
  | zero => simp [qpow, MixedExpr.eval]
  | succ m ih =>
      simp only [qpow, qmul, MixedExpr.eval, CoeffExpr.eval, ih.1, ih.2, ha]
      constructor <;> ring

/-- An Im-free gate: Im evaluates to `0` and Re to the gate at the Re readings. -/
theorem toQ_eval_of_noIm (M : ImMap) (n : ℕ) (hn : n = MemoryTable.pwScaleExp K) (eK : Env K)
    (eF : Env F) : ∀ g : CorrectedFinalTypedExpr, hasIm M g = false →
      (toQ F M n δ g).2.eval eK eF = 0 ∧ (toQ F M n δ g).1.eval eK eF = g.eval (reEnv eK eF)
  | .baseCur i, _ => by simp [toQ, qlift, MixedExpr.eval, CoeffExpr.eval,
      CorrectedFinalTypedExpr.eval, reEnv]
  | .baseNext i, _ => by simp [toQ, qlift, MixedExpr.eval, CoeffExpr.eval,
      CorrectedFinalTypedExpr.eval, reEnv]
  | .extCur i, h => by
      simp only [hasIm, Option.isSome_eq_false_iff, Option.isNone_iff_eq_none] at h
      simp only [toQ, h]; exact ⟨qvar_snd_eval_none .., qvar_fst_eval ..⟩
  | .extNext i, h => by
      simp only [hasIm, Option.isSome_eq_false_iff, Option.isNone_iff_eq_none] at h
      simp only [toQ, h]; exact ⟨qvar_snd_eval_none .., qvar_fst_eval ..⟩
  | .challenge i, h => by
      simp only [hasIm, Option.isSome_eq_false_iff, Option.isNone_iff_eq_none] at h
      simp only [toQ, h]; exact ⟨qvar_snd_eval_none .., qvar_fst_eval ..⟩
  | .extensionPublic i, h => by
      simp only [hasIm, Option.isSome_eq_false_iff, Option.isNone_iff_eq_none] at h
      simp only [toQ, h]; exact ⟨qvar_snd_eval_none .., qvar_fst_eval ..⟩
  | .scalarPublic i, _ => by simp [toQ, qlift, MixedExpr.eval, CoeffExpr.eval,
      CorrectedFinalTypedExpr.eval, reEnv]
  | .const c, _ => by simp [toQ, qconst, MixedExpr.eval, CorrectedFinalTypedExpr.eval]
  | .add x y, h => by
      simp only [hasIm, Bool.or_eq_false_iff] at h
      have hx := toQ_eval_of_noIm M n hn eK eF x h.1
      have hy := toQ_eval_of_noIm M n hn eK eF y h.2
      simp only [toQ, qadd, MixedExpr.eval, CorrectedFinalTypedExpr.eval, hx.1, hx.2, hy.1, hy.2]
      simp
  | .sub x y, h => by
      simp only [hasIm, Bool.or_eq_false_iff] at h
      have hx := toQ_eval_of_noIm M n hn eK eF x h.1
      have hy := toQ_eval_of_noIm M n hn eK eF y h.2
      simp only [toQ, qsub, MixedExpr.eval, CorrectedFinalTypedExpr.eval, hx.1, hx.2, hy.1, hy.2]
      simp
  | .mul x y, h => by
      simp only [hasIm, Bool.or_eq_false_iff] at h
      have hx := toQ_eval_of_noIm M n hn eK eF x h.1
      have hy := toQ_eval_of_noIm M n hn eK eF y h.2
      simp only [toQ, qmul, MixedExpr.eval, CoeffExpr.eval, CorrectedFinalTypedExpr.eval, hx.1, hx.2,
        hy.1, hy.2]
      simp
  | .neg x, h => by
      simp only [hasIm] at h
      have hx := toQ_eval_of_noIm M n hn eK eF x h
      simp only [toQ, qneg, MixedExpr.eval, CorrectedFinalTypedExpr.eval, hx.1, hx.2]
      simp
  | .pow x m, h => by
      simp only [hasIm] at h
      have hx := toQ_eval_of_noIm M n hn eK eF x h
      have hp := qpow_eval_of_im_zero δ eK eF _ hx.1 m
      simp only [toQ, CorrectedFinalTypedExpr.eval]
      exact ⟨hp.2, by rw [hp.1, hx.2]⟩
  | .certBase i, _ => by simp [toQ, qlift, MixedExpr.eval, CoeffExpr.eval,
      CorrectedFinalTypedExpr.eval, reEnv]
  | .certExt i, _ => by
      simp only [toQ]; exact ⟨qvar_snd_eval_none .., qvar_fst_eval ..⟩
  | .lamPow d, h => by
      simp only [hasIm, Option.isSome_eq_false_iff, Option.isNone_iff_eq_none] at h
      simp only [toQ, CorrectedFinalTypedExpr.eval, lamPowVal, ← hn, h]
      split_ifs
      · have hp := qpow_eval_of_im_zero δ eK eF (qvar F .challenge (3 * 9) none)
          (qvar_snd_eval_none ..) (n - d)
        rw [hp.1, hp.2, qvar_fst_eval]; exact ⟨rfl, rfl⟩
      · simp [qconst, MixedExpr.eval]
  | .expCur, _ => by simp [toQ, qlift, MixedExpr.eval, CoeffExpr.eval,
      CorrectedFinalTypedExpr.eval, reEnv]

/-- **Re twin of a linear gate**: the Re half evaluates to the gate at the Re readings. -/
theorem toQ_fst_eval_of_qLinear (M : ImMap) (n : ℕ) (hn : n = MemoryTable.pwScaleExp K)
    (eK : Env K) (eF : Env F) : ∀ g : CorrectedFinalTypedExpr, qLinear M g = true →
      (toQ F M n δ g).1.eval eK eF = g.eval (reEnv eK eF)
  | .baseCur i, _ => (toQ_eval_of_noIm δ M n hn eK eF (.baseCur i) rfl).2
  | .baseNext i, _ => (toQ_eval_of_noIm δ M n hn eK eF (.baseNext i) rfl).2
  | .extCur i, _ => by simp only [toQ]; exact qvar_fst_eval ..
  | .extNext i, _ => by simp only [toQ]; exact qvar_fst_eval ..
  | .challenge i, _ => by simp only [toQ]; exact qvar_fst_eval ..
  | .extensionPublic i, _ => by simp only [toQ]; exact qvar_fst_eval ..
  | .scalarPublic i, _ => (toQ_eval_of_noIm δ M n hn eK eF (.scalarPublic i) rfl).2
  | .const c, _ => (toQ_eval_of_noIm δ M n hn eK eF (.const c) rfl).2
  | .add x y, h => by
      simp only [qLinear, Bool.and_eq_true] at h
      simp only [toQ, qadd, MixedExpr.eval, CorrectedFinalTypedExpr.eval,
        toQ_fst_eval_of_qLinear M n hn eK eF x h.1, toQ_fst_eval_of_qLinear M n hn eK eF y h.2]
  | .sub x y, h => by
      simp only [qLinear, Bool.and_eq_true] at h
      simp only [toQ, qsub, MixedExpr.eval, CorrectedFinalTypedExpr.eval,
        toQ_fst_eval_of_qLinear M n hn eK eF x h.1, toQ_fst_eval_of_qLinear M n hn eK eF y h.2]
  | .mul x y, h => by
      simp only [qLinear, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at h
      rcases h with ⟨hx, hy⟩ | ⟨hx, hy⟩
      · have hx' := toQ_eval_of_noIm δ M n hn eK eF x hx
        simp only [toQ, qmul, MixedExpr.eval, CoeffExpr.eval, CorrectedFinalTypedExpr.eval, hx'.1,
          hx'.2, toQ_fst_eval_of_qLinear M n hn eK eF y hy]
        simp
      · have hy' := toQ_eval_of_noIm δ M n hn eK eF y hy
        simp only [toQ, qmul, MixedExpr.eval, CoeffExpr.eval, CorrectedFinalTypedExpr.eval, hy'.1,
          hy'.2, toQ_fst_eval_of_qLinear M n hn eK eF x hx]
        simp
  | .neg x, h => by
      simp only [qLinear] at h
      simp only [toQ, qneg, MixedExpr.eval, CorrectedFinalTypedExpr.eval,
        toQ_fst_eval_of_qLinear M n hn eK eF x h]
  | .pow x m, h => by
      simp only [qLinear, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true',
        decide_eq_true_eq] at h
      rcases h with hx | ⟨hm, hx⟩
      · exact (toQ_eval_of_noIm δ M n hn eK eF (.pow x m) (by simp [hasIm, hx])).2
      · have ih := toQ_fst_eval_of_qLinear M n hn eK eF x hx
        interval_cases m
        · simp [toQ, qpow, MixedExpr.eval, CorrectedFinalTypedExpr.eval]
        · simp [toQ, qpow, qmul, MixedExpr.eval, CoeffExpr.eval, CorrectedFinalTypedExpr.eval, ih]
  | .certBase i, _ => (toQ_eval_of_noIm δ M n hn eK eF (.certBase i) rfl).2
  | .certExt i, _ => (toQ_eval_of_noIm δ M n hn eK eF (.certExt i) rfl).2
  | .lamPow d, h => by
      simp only [qLinear, Option.isNone_iff_eq_none] at h
      exact (toQ_eval_of_noIm δ M n hn eK eF (.lamPow d) (by simp [hasIm, h])).2
  | .expCur, _ => (toQ_eval_of_noIm δ M n hn eK eF .expCur rfl).2

variable [Fact (¬ IsSquare (algebraMap F K δ))]

/-- **Append-only for linear gates**: the EXISTING compiled gate (the chip's
`correctedFinalTypedCompile`) together with the APPENDED compiled Im twin vanish iff the gate holds
in `𝕂′` at the tower environment. -/
theorem appendOnly_iff [FiniteDimensional F K] (b : Basis (Fin 3) F K) (M : ImMap) (n : ℕ)
    (hn : n = MemoryTable.pwScaleExp K) {eK : Env K} {eF : Env F} (h : IsCoordEnv b col0Id eK eF)
    (g : CorrectedFinalTypedExpr) (hlin : qLinear M g = true) :
    ((∀ k, (correctedFinalTypedCompile b g k).eval eF = 0) ∧
        ∀ k, (mixedCompile b col0Id (toQ F M n δ g).2 k).eval eF = 0) ↔
      g.eval (towerEnv δ M eK eF) = 0 := by
  rw [← toQ_compiled_iff δ b M n hn h g]
  have hre : (∀ k, (correctedFinalTypedCompile b g k).eval eF = 0) ↔
      ∀ k, (mixedCompile b col0Id (toQ F M n δ g).1 k).eval eF = 0 := by
    rw [correctedFinalTypedCompile_zero_iff b (reEnv eK eF) eF (isCorrectedFinalCoordEnv_reEnv b h),
      ← mixedCompile_zero_iff b col0Id h, toQ_fst_eval_of_qLinear δ M n hn eK eF g hlin]
  rw [hre]

end Linear

end TowerD
end VclL.Compute
end Nock.NockVMROM.Thm54
