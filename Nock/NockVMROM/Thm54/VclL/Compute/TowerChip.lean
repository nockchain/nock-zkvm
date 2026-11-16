import Nock.NockVMROM.Thm54.VclL.Compute.TowerD
import Nock.NockVMROM.Thm54.VclL.Compute.ChipQ7S

/-!
# Route (d), phase 2 : the tower gates of the Q7S compute chip

## The reindex

`computeChipVCLQ7S`'s gates are `reindexE` of the width-309 source gates (`vclCol`: `i < 202` fixed,
`302 ↦ 220`, `i ≥ 303 ↦ i - 95`).  `fullImMap` names the APPENDED Im columns in the TARGET layout
(`232.. 393`), but the typed gates are translated in the SOURCE layout, so the Im columns must be
named by their source preimage `c + 95 ≥ 327` (`shiftIm`, `towerM`): `vclCol (c + 95) = c`
(`vclCol_im`).  No existing column constant moves.

## What this module proves (generic in `F`, `K`, `b`, `δ`)

* `towerM` columns are outside Form R and past the source width (`towerM_cols`);
* `colsIn_mixedCompile` / `toQ_colsOk` / `toQW_colsOk`: every compiled twin reads only `NoFormR`
  columns, so `eval_reindexE` applies;
* the twin gate lists `coreRe`, `coreIm`, `auxIm`, `epIm` and the per-gate transport
  `coreGate_iff` (a core gate holds in `𝕂′` at `towerEnv` iff its Re body and its Im twin vanish).
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
open Nock.NockVMROM.Thm54.VclL.Compute.LnRead

set_option autoImplicit false
set_option maxRecDepth 300000
set_option linter.unusedSectionVars false

noncomputable section

/-! ## 1. The source-layout Im map -/

/-- Name the appended Im columns by their SOURCE preimage (`vclCol (c + 95) = c`). -/
def shiftIm (M : ImMap) : ImMap :=
  { M with ext := fun r => (M.ext r).map (· + 95), walk := fun j => (M.walk j).map (· + 95) }

/-- **The tower Im map in the source layout.** -/
def towerM : ImMap := shiftIm fullImMap

theorem vclCol_im (c : ℕ) (h : 232 ≤ c) : vclCol (c + 95) = c := by
  simp only [vclCol, serialCol]; split_ifs <;> omega

/-- Every Im triple of `towerM` is a source column outside Form R (and `≥ 327`, so it collides with
no source column). -/
theorem towerM_cols :
    (∀ r : Fin 63, (towerM.ext r).elim true (fun c => decide (327 ≤ c)) = true) ∧
    (∀ j : Fin 2, (towerM.walk j).elim true (fun c => decide (327 ≤ c)) = true) := by
  constructor <;> decide +kernel

theorem towerM_ext_ge (r : Fin 63) (c : ℕ) (h : towerM.ext r = some c) : 327 ≤ c := by
  have := towerM_cols.1 r
  rw [h] at this
  simpa using this

theorem towerM_walk_ge (j : Fin 2) (c : ℕ) (h : towerM.walk j = some c) : 327 ≤ c := by
  have := towerM_cols.2 j
  rw [h] at this
  simpa using this

/-- The `w59` Im column (source layout). -/
def walkAccImCol : ℕ := (towerM.ext 59).getD 0

theorem towerM_chal : towerM.chal = towerChal := rfl
theorem towerM_pub : towerM.extPub = fullImMap.extPub := rfl

/-! ## 2. Column support of the compiled twins -/

section ColsOk
variable {F K : Type} [Field F] [Field K] [Algebra F K]

/-- Every trace column a `MixedExpr` reads (through its three-limb window) satisfies `P`. -/
def ColsOk (P : ℕ → Prop) : MixedExpr F → Prop
  | .Var .traceCur i => ∀ k : Fin 3, P (i + k)
  | .Var .traceNext i => ∀ k : Fin 3, P (i + k)
  | .Var _ _ => True
  | .Lift g => ColsIn P g
  | .Scale g u => ColsIn P g ∧ ColsOk P u
  | .Const _ => True
  | .Add x y => ColsOk P x ∧ ColsOk P y
  | .Sub x y => ColsOk P x ∧ ColsOk P y
  | .Mul x y => ColsOk P x ∧ ColsOk P y
  | .Neg x => ColsOk P x
  | .Pow x _ => ColsOk P x

theorem colsIn_mixedCompile {P : ℕ → Prop} (b : Basis (Fin 3) F K) :
    ∀ (E : MixedExpr F), ColsOk P E → ∀ k : Fin 3, ColsIn P (mixedCompile b col0Id E k)
  | .Var .traceCur i, h, k => colsIn_var _ _ (h k)
  | .Var .traceNext i, h, k => colsIn_var _ _ (h k)
  | .Var .challenge i, _, k => by simp [mixedCompile, ColsIn, colsOf]
  | .Var .publicVal i, _, k => by simp [mixedCompile, ColsIn, colsOf]
  | .Lift g, h, k => colsIn_mul (colsIn_const _) h
  | .Scale g u, h, k => colsIn_mul h.1 (colsIn_mixedCompile b u h.2 k)
  | .Const c, _, k => colsIn_const _
  | .Add x y, h, k => colsIn_add (colsIn_mixedCompile b x h.1 k) (colsIn_mixedCompile b y h.2 k)
  | .Sub x y, h, k => colsIn_sub (colsIn_mixedCompile b x h.1 k) (colsIn_mixedCompile b y h.2 k)
  | .Neg x, h, k => colsIn_neg (colsIn_mixedCompile b x h k)
  | .Mul x y, h, k => colsIn_mulVec b _ _ (fun i => colsIn_mixedCompile b x h.1 i)
      (fun i => colsIn_mixedCompile b y h.2 i) k
  | .Pow x n, h, k => colsIn_powVec b _ (fun i => colsIn_mixedCompile b x h i) n k

/-- A pair is column-OK when both halves are. -/
def QOk (P : ℕ → Prop) (q : Q F) : Prop := ColsOk P q.1 ∧ ColsOk P q.2

theorem qOk_add {P : ℕ → Prop} {a b : Q F} (ha : QOk P a) (hb : QOk P b) : QOk P (qadd F a b) :=
  ⟨⟨ha.1, hb.1⟩, ⟨ha.2, hb.2⟩⟩
theorem qOk_sub {P : ℕ → Prop} {a b : Q F} (ha : QOk P a) (hb : QOk P b) : QOk P (qsub F a b) :=
  ⟨⟨ha.1, hb.1⟩, ⟨ha.2, hb.2⟩⟩
theorem qOk_neg {P : ℕ → Prop} {a : Q F} (ha : QOk P a) : QOk P (qneg F a) := ⟨ha.1, ha.2⟩
theorem qOk_mul {P : ℕ → Prop} (δ : F) {a b : Q F} (ha : QOk P a) (hb : QOk P b) :
    QOk P (qmul F δ a b) :=
  ⟨⟨⟨ha.1, hb.1⟩, colsIn_const _, ⟨ha.2, hb.2⟩⟩, ⟨⟨ha.1, hb.2⟩, ⟨ha.2, hb.1⟩⟩⟩
theorem qOk_pow {P : ℕ → Prop} (δ : F) {a : Q F} (ha : QOk P a) :
    ∀ n, QOk P (qpow F δ a n)
  | 0 => ⟨trivial, trivial⟩
  | n + 1 => qOk_mul δ ha (qOk_pow δ ha n)
theorem qOk_lift {P : ℕ → Prop} {g : CoeffExpr F} (hg : ColsIn P g) : QOk P (qlift F g) :=
  ⟨hg, trivial⟩
theorem qOk_const {P : ℕ → Prop} (c : ℤ) : QOk P (qconst F c) := ⟨trivial, trivial⟩

/-- A `qvar` is column-OK when its Re window and (if present) Im window are. -/
theorem qOk_var {P : ℕ → Prop} (kind : VarKind) (re : ℕ) (im : Option ℕ)
    (hre : kind = .traceCur ∨ kind = .traceNext → ∀ k : Fin 3, P (re + k))
    (him : ∀ c, im = some c → (kind = .traceCur ∨ kind = .traceNext) → ∀ k : Fin 3, P (c + k)) :
    QOk P (qvar F kind re im) := by
  cases kind <;> cases im <;> simp_all [qvar, QOk, ColsOk]

/-- **Every translated typed gate (no Form R leaf) is column-OK** at the source layout. -/
theorem toQ_colsOk (δ : F) (M : ImMap) (n : ℕ)
    (hM : ∀ r c, M.ext r = some c → ∀ k : Fin 3, NoFormR (c + k)) :
    ∀ t : CorrectedFinalTypedExpr, tNoCert t = true → QOk NoFormR (toQ F M n δ t)
  | .baseCur i, _ => qOk_lift (colsIn_var _ _ (Or.inl (by have := i.isLt; omega)))
  | .baseNext i, _ => qOk_lift (colsIn_var _ _ (Or.inl (by have := i.isLt; omega)))
  | .extCur i, _ => qOk_var _ _ _
      (fun _ k => Or.inl (by have := i.isLt; have := k.isLt; omega))
      (fun c hc _ => hM i c hc)
  | .extNext i, _ => qOk_var _ _ _
      (fun _ k => Or.inl (by have := i.isLt; have := k.isLt; omega))
      (fun c hc _ => hM i c hc)
  | .challenge i, _ => qOk_var _ _ _ (fun h => by rcases h with h | h <;> cases h)
      (fun c _ h => by rcases h with h | h <;> cases h)
  | .extensionPublic i, _ => qOk_var _ _ _ (fun h => by rcases h with h | h <;> cases h)
      (fun c _ h => by rcases h with h | h <;> cases h)
  | .scalarPublic i, _ => qOk_lift (by simp [ColsIn, colsOf])
  | .const c, _ => qOk_const c
  | .add x y, h => by
      simp only [tNoCert, Bool.and_eq_true] at h
      exact qOk_add (toQ_colsOk δ M n hM x h.1) (toQ_colsOk δ M n hM y h.2)
  | .sub x y, h => by
      simp only [tNoCert, Bool.and_eq_true] at h
      exact qOk_sub (toQ_colsOk δ M n hM x h.1) (toQ_colsOk δ M n hM y h.2)
  | .mul x y, h => by
      simp only [tNoCert, Bool.and_eq_true] at h
      exact qOk_mul δ (toQ_colsOk δ M n hM x h.1) (toQ_colsOk δ M n hM y h.2)
  | .neg x, h => qOk_neg (toQ_colsOk δ M n hM x h)
  | .pow x m, h => qOk_pow δ (toQ_colsOk δ M n hM x h) m
  | .certBase i, h => by simp [tNoCert] at h
  | .certExt i, h => by simp [tNoCert] at h
  | .lamPow d, _ => by
      simp only [toQ]
      split_ifs
      · exact qOk_pow δ (qOk_var _ _ _ (fun h => by rcases h with h | h <;> cases h)
          (fun c _ h => by rcases h with h | h <;> cases h)) _
      · exact qOk_const 0
  | .expCur, _ => qOk_lift (colsIn_var _ _ (Or.inr (le_refl _)))

theorem toQW_colsOk (δ : F) (M : ImMap) (n : ℕ)
    (hM : ∀ r c, M.ext r = some c → ∀ k : Fin 3, NoFormR (c + k))
    (hW : ∀ j c, M.walk j = some c → ∀ k : Fin 3, NoFormR (c + k)) :
    ∀ t : WTyped, wNoCert t = true → QOk NoFormR (toQW F M n δ t)
  | .leaf t, h => toQ_colsOk δ M n hM t h
  | .wCur j, _ => qOk_var _ _ _ (fun _ k => Or.inr (by have := j.isLt; have := k.isLt; omega))
      (fun c hc _ => hW j c hc)
  | .wNext j, _ => qOk_var _ _ _ (fun _ k => Or.inr (by have := j.isLt; have := k.isLt; omega))
      (fun c hc _ => hW j c hc)
  | .add x y, h => by
      simp only [wNoCert, Bool.and_eq_true] at h
      exact qOk_add (toQW_colsOk δ M n hM hW x h.1) (toQW_colsOk δ M n hM hW y h.2)
  | .sub x y, h => by
      simp only [wNoCert, Bool.and_eq_true] at h
      exact qOk_sub (toQW_colsOk δ M n hM hW x h.1) (toQW_colsOk δ M n hM hW y h.2)
  | .mul x y, h => by
      simp only [wNoCert, Bool.and_eq_true] at h
      exact qOk_mul δ (toQW_colsOk δ M n hM hW x h.1) (toQW_colsOk δ M n hM hW y h.2)
  | .neg x, h => qOk_neg (toQW_colsOk δ M n hM hW x h)
  | .pow x m, h => qOk_pow δ (toQW_colsOk δ M n hM hW x h) m

end ColsOk

theorem towerM_noFormR : (∀ r c, towerM.ext r = some c → ∀ k : Fin 3, NoFormR (c + k)) ∧
    (∀ j c, towerM.walk j = some c → ∀ k : Fin 3, NoFormR (c + k)) :=
  ⟨fun r c h k => Or.inr (by have := towerM_ext_ge r c h; omega),
   fun j c h k => Or.inr (by have := towerM_walk_ge j c h; omega)⟩

/-! ## 3. The core twin gates -/

section Gates
variable {F K : Type} [Field F] [Field K] [Algebra F K]

/-- The core ids whose chip body is not the typed gate's compilation (`72..77`, `81`: the `notLast`
masked / residual-witness / queue / chain forms). -/
def specialCore (i : CorrectedCoreExtGateId) : Bool :=
  decide (72 ≤ i.val ∧ i.val ≤ 77) || decide (i.val = 81)

def coreRe (b : Basis (Fin 3) F K) (δ : F) (n : ℕ) (M : ImMap) (i : CorrectedCoreExtGateId)
    (k : Fin 3) : CoeffExpr F :=
  if specialCore i || qLinear M (correctedFinalExtGate i) then correctedCoreCoord309 b i k
  else mixedCompile b col0Id (toQ F M n δ (correctedFinalExtGate i)).1 k

/-- **The Im twin of core gate `i`**: `(toQ g).2` compiled; the walk-accumulator residual (`75`,
`notLast · role 59`) has Im `notLast · Im(role 59)`. -/
def coreIm (b : Basis (Fin 3) F K) (δ : F) (n : ℕ) (M : ImMap) (i : CorrectedCoreExtGateId)
    (k : Fin 3) : CoeffExpr F :=
  if i = packedWalkAccId then .mul OptimizedComputeFinal.notLastCoeff (.var .traceCur (walkAccImCol + (k : ℕ)))
  else mixedCompile b col0Id (toQ F M n δ (correctedFinalExtGate i)).2 k

/-- The kept core ids that carry an Im twin. -/
def coreImIds (M : ImMap) : List CorrectedCoreExtGateId :=
  keptCoreIdsQ7.filter fun i =>
    decide (i = packedWalkAccId) || (!specialCore i && hasIm M (correctedFinalExtGate i))

theorem coord_zero' (b : Basis (Fin 3) F K) (k : Fin 3) : coord b (0 : K) k = 0 := by
  simp [coord]

/-- An Im-free gate's Im twin vanishes. -/
theorem imTwin_zero_of_noIm [FiniteDimensional F K] (b : Basis (Fin 3) F K) (δ : F) (M : ImMap)
    (n : ℕ) (hn : n = MemoryTable.pwScaleExp K) {eK : Env K} {eF : Env F}
    (h : IsCoordEnv b col0Id eK eF) (g : CorrectedFinalTypedExpr) (hg : hasIm M g = false)
    (k : Fin 3) : (mixedCompile b col0Id (toQ F M n δ g).2 k).eval eF = 0 := by
  rw [← mixedCompile_eval b col0Id h, (toQ_eval_of_noIm δ M n hn eK eF g hg).1]
  exact coord_zero' b k

theorem coreCoord309_of_not_special (b : Basis (Fin 3) F K) (i : CorrectedCoreExtGateId)
    (hs : specialCore i = false) (k : Fin 3) :
    correctedCoreCoord309 b i k = correctedFinalTypedCompile b (correctedFinalExtGate i) k := by
  have hv : ¬ (72 ≤ i.val ∧ i.val ≤ 77) ∧ i.val ≠ 81 := by
    simpa [specialCore] using hs
  have h : ∀ j : CorrectedCoreExtGateId, (72 ≤ j.val ∧ j.val ≤ 77) ∨ j.val = 81 → j ≠ i :=
    fun j hj hji => by subst hji; omega
  have h72 := h packedLnChainId (by simp)
  have h73 := h packedWalkLnId (by simp)
  have h74 := h packedWalkCountId (by simp)
  have h75 := h packedWalkAccId (by simp)
  have h76 := h packedQueueNonEmptyId (by simp)
  have h77 := h packedQueueTilingId (by simp)
  have h81 := h packedChainId (by simp)
  simp only [correctedCoreCoord309, correctedCoreCoord]
  simp [h72.symm, h73.symm, h74.symm, h75.symm, h76.symm,
    h77.symm, h81.symm]

/-- **The core transport**: a (non-special) core gate holds in `𝕂′` at `towerEnv` iff its Re body
and (when it carries an Im half) its Im twin vanish. -/
theorem coreGate_iff [FiniteDimensional F K] (b : Basis (Fin 3) F K) (δ : F)
    [Fact (¬ IsSquare (algebraMap F K δ))] (M : ImMap)
    (n : ℕ) (hn : n = MemoryTable.pwScaleExp K) {eK : Env K} {eF : Env F}
    (h : IsCoordEnv b col0Id eK eF) (i : CorrectedCoreExtGateId) (hs : specialCore i = false) :
    ((∀ k, (coreRe b δ n M i k).eval eF = 0) ∧
        (hasIm M (correctedFinalExtGate i) = true → ∀ k, (coreIm b δ n M i k).eval eF = 0)) ↔
      CorrectedFinalTypedExpr.eval (towerEnv δ M eK eF) (correctedFinalExtGate i) = 0 := by
  have hne : i ≠ packedWalkAccId := by
    intro hh; subst hh; simp [specialCore] at hs
  have himE : ∀ k, coreIm b δ n M i k =
      mixedCompile b col0Id (toQ F M n δ (correctedFinalExtGate i)).2 k := fun k => by
    simp [coreIm, hne]
  by_cases hl : qLinear M (correctedFinalExtGate i) = true
  · have hre : ∀ k, coreRe b δ n M i k =
        correctedFinalTypedCompile b (correctedFinalExtGate i) k := fun k => by
      simp [coreRe, hs, hl, coreCoord309_of_not_special b i hs]
    rw [← appendOnly_iff δ b M n hn h _ hl]
    simp only [hre, himE]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨h1, fun k => ?_⟩
      rcases Bool.eq_false_or_eq_true (hasIm M (correctedFinalExtGate i)) with hi | hi
      · exact h2 hi k
      · exact imTwin_zero_of_noIm b δ M n hn h _ hi k
    · rintro ⟨h1, h2⟩; exact ⟨h1, fun _ => h2⟩
  · have hre : ∀ k, coreRe b δ n M i k =
        mixedCompile b col0Id (toQ F M n δ (correctedFinalExtGate i)).1 k := fun k => by
      simp [coreRe, hs, hl]
    rw [← toQ_compiled_iff δ b M n hn h _]
    simp only [hre, himE]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨h1, fun k => ?_⟩
      rcases Bool.eq_false_or_eq_true (hasIm M (correctedFinalExtGate i)) with hi | hi
      · exact h2 hi k
      · exact imTwin_zero_of_noIm b δ M n hn h _ hi k
    · rintro ⟨h1, h2⟩; exact ⟨h1, fun _ => h2⟩

end Gates

end

end TowerD
end VclL.Compute
end Nock.NockVMROM.Thm54
