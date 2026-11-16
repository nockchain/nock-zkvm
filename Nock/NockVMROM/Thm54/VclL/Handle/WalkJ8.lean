/-
  Nock/NockVMROM/Thm54/VclL/Handle/WalkJ8.lean

`walkTemplateJ8` is `walkTemplateHQK` with exactly two base gates changed: the depth certificate
  `len + Σ_{i<6} 2^i bᵢ − 61` is retyped to `len + Σ_{i<5} 2^i bᵢ + 29·b₅ − 60` and the exclusion
  `u·b₃·b₄·b₅` is dropped (`walkJ8_unchanged`: every other list is literally `walkTemplateHQK`'s).
  Width `166` (`walkChipJ8_width`), degree `≤ 4`.  The six bits now certify `len ∈ [0, 60]`
  (`HalvingJ8.depthCert60_range`).

  **Soundness by reduction, not by copying W1–W3.**  `bitFix` replaces the seven certificate columns
  `u, b₀..b₅` (`14..20`) of an accepted `walkChipJ8` trace by Lagrange interpolants over the row set
  of the OLD certificate of the same `len` (`61 − len`, which is in `[1, 61]` because `len ≤ 60`).  No
  other gate reads those columns (`avC` / `avM`, checked by evaluation), so `bitFix Q` is accepted by
  `walkChipHQK` (`walkChipJ8_bitFix_sat`, `_bind`) and agrees with `Q` on every other column
  (`bitFix_off`).  Every W1–W3 theorem stated for `walkChipHQK` (`atomWalk_records_genuine`, the
  cell-walk lemmas through `restrictWalkK`) therefore applies to `bitFix Q` verbatim, at the
  UNCHANGED `walkEvent` (Dmax `62`): no priced event changes shape.  The narrowed bound enters as an
  extra fact, `walkJ8_len_le_60` (every row's `natOf len ≤ 60`).
-/
import Nock.NockVMROM.Thm54.VclL.Handle.AtomWalkAW
import Nock.NockVMROM.Thm54.VclL.Handle.HalvingJ8
import Mathlib.LinearAlgebra.Lagrange

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false

namespace Nock.NockVMROM.Thm54.VclL.Handle.WalkJ8

open Nock Nock.Reified Nock.Framework Nock.Walk
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.WalkVCL
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.VclL.Handle Nock.NockVMROM.Thm54.VclL.Handle.CellTwinK
open Nock.NockVMROM.Thm54.VclL.Handle.AtomWalkAW
open Module
open scoped Polynomial

noncomputable section

/-! ## 1. The gates -/

section Gates
variable {F : Type} [Field F]

/-- The narrowed depth certificate `len + Σ_{i<5} 2^i bᵢ + 29·b₅ − 60`. -/
def depthJ8 : CoeffExpr F :=
  .sub (.add (.add (cv WChip.len) (bitSum WChip.bit0 5)) (.mul (.const 29) (WChip.bt 5))) (.const 60)

/-- The deployed depth certificate and exclusion (dropped at J-8). -/
def depthOld : CoeffExpr F := .sub (.add (cv WChip.len) (bitSum WChip.bit0 6)) (.const 61)
def exclOld : CoeffExpr F := .mul (.mul (cv WChip.u) (WChip.bt 3)) (.mul (WChip.bt 4) (WChip.bt 5))

/-- The base gates before the certificate (`cL, cR` booleanity, `e = cL·cR`, `u = b₁b₂`). -/
def basePre : List (CoeffExpr F) :=
  [ boolE (cv WChip.cL), boolE (cv WChip.cR), .sub (cv WChip.e) (.mul (cv WChip.cL) (cv WChip.cR)),
    .sub (cv WChip.u) (.mul (WChip.bt 1) (WChip.bt 2)) ]

/-- The base gates after the certificate (root gate, queue counter, bit booleanity). -/
def basePost (kroots : ℕ) : List (CoeffExpr F) :=
  [ .mul (cv WChip.rM) (.sub (cv WChip.pre) (.const 1)),
    .mul (cv WChip.rM) (cv WChip.len),
    .mul (cv WChip.rM) (.sub (cv WChip.ridx) (cv WChip.idx)),
    .mul (cv WChip.isF) (.add (.sub (.sub (.sub (cv WChip.q) (.const (kroots : F))) (cv WChip.cL))
      (cv WChip.cR)) (.const 1)),
    .mul (notE (cv WChip.isL)) (.add (.sub (.sub (.sub (nv WChip.q) (cv WChip.q)) (nv WChip.cL))
      (nv WChip.cR)) (.const 1)),
    .mul (notE (cv WChip.isL)) (.sub (.mul (cv WChip.q) (cv WChip.qinv)) (.const 1)),
    .mul (cv WChip.isL) (cv WChip.q) ] ++
  (List.range 6).map fun i => boolE (WChip.bt i)

/-- **The deployed walk base gates split around the certificate** (`rfl`). -/
theorem baseGates_split (kroots : ℕ) :
    WChip.baseGates (F := F) kroots = basePre ++ [exclOld, depthOld] ++ basePost kroots := rfl

/-- **The J-8 walk base gates**: the certificate retyped, the exclusion dropped. -/
def baseGatesJ8 (kroots : ℕ) : List (CoeffExpr F) := basePre ++ [depthJ8] ++ basePost kroots

theorem depthJ8_deg : (depthJ8 : CoeffExpr F).degree ≤ 4 := by
  simp [depthJ8, bitSum_degree_le4, CoeffExpr.degree]

theorem baseGatesJ8_deg (kroots : ℕ) : ∀ g ∈ baseGatesJ8 (F := F) kroots ++ baseHK, g.degree ≤ 4 := by
  intro g hg
  have hold := baseHK_deg (F := F) kroots
  simp only [baseGatesJ8, List.mem_append, List.mem_singleton] at hg
  rcases hg with ((hg | rfl) | hg) | hg
  · exact hold g (List.mem_append_left _ (by rw [baseGates_split]; simp [hg]))
  · exact depthJ8_deg
  · exact hold g (List.mem_append_left _ (by rw [baseGates_split]; simp [hg]))
  · exact hold g (List.mem_append_right _ hg)

end Gates

/-! ## 2. The template and the chip -/

section Template
variable {F : Type} [Field F]

/-- **`walkTemplateJ8`**: `walkTemplateHQK` with only the depth certificate retyped. -/
def walkTemplateJ8 (δF : F) (kroots : ℕ) : ChipTemplate F where
  rounds := 3
  rounds_pos := by decide
  baseColsOf := ![25, 0, 0]
  extColsOf := ![0, 24, 23]
  baseTransition := baseGatesJ8 kroots ++ baseHK
  extTransition := []
  mixedTransition := WChip.mixedGates δF kroots ++ WalkHQ.gates δF
  extDeg1 := []
  extDeg3 := []
  equalityChecks := []
  baseTransition_deg := baseGatesJ8_deg kroots
  extTransition_deg := by simp
  mixedTransition_deg := WalkHQ.mixed_deg δF kroots
  extDeg1_deg := by simp
  extDeg3_deg := by simp
  equalityChecks_deg := by simp

/-- **Everything but the two certificate gates is literally `walkTemplateHQK`'s** (list equalities). -/
theorem walkJ8_unchanged (δF : F) (kroots : ℕ) :
    (walkTemplateHQK δF kroots).baseTransition =
      basePre ++ [exclOld, depthOld] ++ basePost kroots ++ baseHK ∧
    (walkTemplateJ8 δF kroots).baseTransition = basePre ++ [depthJ8] ++ basePost kroots ++ baseHK ∧
    (walkTemplateJ8 δF kroots).mixedTransition = (walkTemplateHQK δF kroots).mixedTransition ∧
    (walkTemplateJ8 δF kroots).extTransition = (walkTemplateHQK δF kroots).extTransition ∧
    (walkTemplateJ8 δF kroots).extDeg1 = (walkTemplateHQK δF kroots).extDeg1 ∧
    (walkTemplateJ8 δF kroots).extDeg3 = (walkTemplateHQK δF kroots).extDeg3 ∧
    (walkTemplateJ8 δF kroots).equalityChecks = (walkTemplateHQK δF kroots).equalityChecks ∧
    (walkTemplateJ8 δF kroots).baseColsOf = (walkTemplateHQK δF kroots).baseColsOf ∧
    (walkTemplateJ8 δF kroots).extColsOf = (walkTemplateHQK δF kroots).extColsOf :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem walkTemplateJ8_baseCols (δF : F) (kroots : ℕ) : (walkTemplateJ8 δF kroots).baseCols = 25 := by
  show (∑ r : Fin 3, (![25, 0, 0] : Fin 3 → ℕ) r) = 25
  decide
theorem walkTemplateJ8_extCols (δF : F) (kroots : ℕ) : (walkTemplateJ8 δF kroots).extCols = 47 := by
  show (∑ r : Fin 3, (![0, 24, 23] : Fin 3 → ℕ) r) = 47
  decide

theorem walkTemplateJ8_width (δF : F) (kroots : ℕ) : (walkTemplateJ8 δF kroots).width 3 = 166 := by
  unfold ChipTemplate.width; rw [walkTemplateJ8_baseCols, walkTemplateJ8_extCols]

/-- **The J-8 walk chip** (masks `0..2`, as `walkChipHQK`). -/
def walkChipJ8 {K : Type} [Field K] [Algebra F K] [FiniteDimensional F K]
    (δF : F) (kroots : ℕ) (b : Basis (Fin 3) F K) {h n : ℕ} (hn : 0 < n)
    (nodes : Fin n → F) (orbit : StrictOrbitDomain F 3 h) (chals pubs : ℕ → K) :
    FixedPreprocessingRAP F where
  rap := expandChip (walkTemplateJ8 δF kroots) b (slotVal b 25 chals) (slotVal b 25 pubs) orbit
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

/-- **Width `166`** (`rfl`-level, as `walkChipHQK`). -/
theorem walkChipJ8_width {K : Type} [Field K] [Algebra F K] [FiniteDimensional F K]
    (δF : F) (kroots : ℕ) (b : Basis (Fin 3) F K) {h n : ℕ} (hn : 0 < n)
    (nodes : Fin n → F) (orbit : StrictOrbitDomain F 3 h) (chals pubs : ℕ → K) :
    (walkChipJ8 δF kroots b hn nodes orbit chals pubs).rap.w = 166 :=
  (walkTemplateJ8_width δF kroots : (walkTemplateJ8 δF kroots).baseCols + (walkTemplateJ8 δF kroots).extCols * 3 = 166)

end Template

/-! ## 3. Columns `14..20` are read by no other gate -/

section Avoid
variable {F : Type} [Field F]

/-- A base expression reads no `traceCur`/`traceNext` column in `[14, 21)`. -/
def avC : CoeffExpr F → Bool
  | .const _ => true
  | .var .traceCur i => decide (i < 14 ∨ 21 ≤ i)
  | .var .traceNext i => decide (i < 14 ∨ 21 ≤ i)
  | .var .challenge _ => true
  | .var .publicVal _ => true
  | .add a b => avC a && avC b
  | .sub a b => avC a && avC b
  | .mul a b => avC a && avC b
  | .neg a => avC a
  | .pow a _ => avC a

/-- A mixed expression's base leaves avoid `[14, 21)`. -/
def avM : MixedExpr F → Bool
  | .Var _ _ => true
  | .Lift g => avC g
  | .Scale g u => avC g && avM u
  | .Const _ => true
  | .Add x y => avM x && avM y
  | .Sub x y => avM x && avM y
  | .Neg x => avM x
  | .Mul x y => avM x && avM y
  | .Pow x _ => avM x

/-- Two base environments agreeing off `[14, 21)`. -/
def AgreeOff (e e' : Env F) : Prop :=
  (∀ j, (j < 14 ∨ 21 ≤ j) → e.trace j = e'.trace j ∧ e.traceNext j = e'.traceNext j) ∧
    e.chal = e'.chal ∧ e.pub = e'.pub

theorem avC_eval {e e' : Env F} (h : AgreeOff e e') : ∀ g : CoeffExpr F, avC g = true →
    g.eval e = g.eval e'
  | .const _, _ => rfl
  | .var .traceCur i, hg => by
      simp only [avC, decide_eq_true_eq] at hg; exact (h.1 i hg).1
  | .var .traceNext i, hg => by
      simp only [avC, decide_eq_true_eq] at hg; exact (h.1 i hg).2
  | .var .challenge i, _ => by simp only [CoeffExpr.eval, h.2.1]
  | .var .publicVal i, _ => by simp only [CoeffExpr.eval, h.2.2]
  | .add a b, hg => by
      simp only [avC, Bool.and_eq_true] at hg
      simp only [CoeffExpr.eval, avC_eval h a hg.1, avC_eval h b hg.2]
  | .sub a b, hg => by
      simp only [avC, Bool.and_eq_true] at hg
      simp only [CoeffExpr.eval, avC_eval h a hg.1, avC_eval h b hg.2]
  | .mul a b, hg => by
      simp only [avC, Bool.and_eq_true] at hg
      simp only [CoeffExpr.eval, avC_eval h a hg.1, avC_eval h b hg.2]
  | .neg a, hg => by simp only [avC] at hg; simp only [CoeffExpr.eval, avC_eval h a hg]
  | .pow a _, hg => by simp only [avC] at hg; simp only [CoeffExpr.eval, avC_eval h a hg]

theorem avM_eval {K : Type} [Field K] [Algebra F K] {e e' : Env F} (h : AgreeOff e e') (eK : Env K) :
    ∀ g : MixedExpr F, avM g = true → g.eval eK e = g.eval eK e'
  | .Var .traceCur _, _ => rfl
  | .Var .traceNext _, _ => rfl
  | .Var .challenge _, _ => rfl
  | .Var .publicVal _, _ => rfl
  | .Lift g, hg => by simp only [avM] at hg; simp only [MixedExpr.eval, avC_eval h g hg]
  | .Scale g u, hg => by
      simp only [avM, Bool.and_eq_true] at hg
      simp only [MixedExpr.eval, avC_eval h g hg.1, avM_eval h eK u hg.2]
  | .Const _, _ => rfl
  | .Add x y, hg => by
      simp only [avM, Bool.and_eq_true] at hg
      simp only [MixedExpr.eval, avM_eval h eK x hg.1, avM_eval h eK y hg.2]
  | .Sub x y, hg => by
      simp only [avM, Bool.and_eq_true] at hg
      simp only [MixedExpr.eval, avM_eval h eK x hg.1, avM_eval h eK y hg.2]
  | .Neg x, hg => by simp only [avM] at hg; simp only [MixedExpr.eval, avM_eval h eK x hg]
  | .Mul x y, hg => by
      simp only [avM, Bool.and_eq_true] at hg
      simp only [MixedExpr.eval, avM_eval h eK x hg.1, avM_eval h eK y hg.2]
  | .Pow x _, hg => by simp only [avM] at hg; simp only [MixedExpr.eval, avM_eval h eK x hg]

theorem basePost_av (kroots : ℕ) : ∀ g ∈ (basePost (F := F) kroots).take 7, avC g = true := by
  intro g hg
  simp [basePost] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [avC, boolE, notE, cv, nv, WChip.rM, WChip.pre, WChip.len, WChip.ridx, WChip.idx,
      WChip.isF, WChip.isL, WChip.q, WChip.qinv, WChip.cL, WChip.cR]

theorem basePre_av : ∀ g ∈ (basePre (F := F)).take 3, avC g = true := by
  intro g hg
  simp [basePre] at hg
  rcases hg with rfl | rfl | rfl <;> simp [avC, boolE, cv, WChip.cL, WChip.cR, WChip.e]

theorem baseHK_av : ∀ g ∈ (baseHK : List (CoeffExpr F)), avC g = true := by
  intro g hg
  simp [baseHK] at hg
  rcases hg with rfl | rfl <;> simp [avC, ternE, cv, WalkHC.kL, WalkHC.kR]

theorem walkMixed_av (δF : F) (kroots : ℕ) : ∀ g ∈ WChip.mixedGates δF kroots, avM g = true := by
  have hall : (WChip.mixedGates δF kroots).all avM = true := by
    simp [WChip.mixedGates, WChip.walkGates, WChip.qEqs, WChip.xKey, WChip.recL, WChip.recR,
      WChip.pTerm, WChip.curW, WChip.childLW, WChip.childRW, WChip.afoW, WChip.ccW, WChip.αk,
      WChip.αE, WChip.γE, WChip.rlcW, WChip.sumME, WChip.vecAt, List.ofFn_succ, QE.gates, QE.var,
      QE.next, QE.chal, QE.pub, QE.base, QE.zero, QE.one, QE.add, QE.sub, QE.mul, QE.scale,
      QE.rlc, QE.gpow, QFP.var, QFP.next, QFP.entries, QFP.sub, QFP.add, QFP.scale, QFP.gates, den,
      rQ, avM, avC, WChip.pR, WChip.lR, WChip.rR, WChip.rootR, WChip.lnR,
      WChip.cntR, WChip.accR, WChip.xInv, WChip.pInvL, WChip.pInvR, WChip.xAcc, WChip.pAcc,
      WChip.isF, WChip.isL, WChip.rM, WChip.idx, WChip.pre, WChip.ridx, WChip.len, WChip.cL,
      WChip.cR, WChip.e, WChip.mL, WChip.mR, cv, nv, notE, boolE]
  intro g hg
  exact List.all_eq_true.mp hall g hg

theorem walkHQ_av (δF : F) : ∀ g ∈ WalkHQ.gates δF, avM g = true := by
  have hall : (WalkHQ.gates δF).all avM = true := by
    simp [WalkHQ.gates, WalkHQ.gatesQ, WalkHQ.pTermQ, HQ.denKeyQ, HQ.rlcQ, HQ.gpowQ, HQ.gamQ,
      HQ.rhoQ, WalkHC.xKeyH, WalkHC.recLH, WalkHC.recRH, QE.gates, QE.var, QE.next, QE.chal,
      QE.pub, QE.base, QE.zero, QE.one, QE.add, QE.sub, QE.mul, QE.scale, avM, avC, cv, nv, notE,
      WChip.isF, WChip.isL, WChip.mL, WChip.mR, WChip.pre, WChip.ridx, WChip.idx,
      WalkHC.kL, WalkHC.kR, WalkHC.vL, WalkHC.vR]
  intro g hg
  exact List.all_eq_true.mp hall g hg

end Avoid

/-! ## 4. The two certificates on one row -/

section Cert
variable {F : Type} [Field F]

theorem bool_nat {x : F} (h : x * (x - 1) = 0) : ∃ β : ℕ, β ≤ 1 ∧ x = (β : F) := by
  rcases mul_eq_zero.mp h with h | h
  · exact ⟨0, by omega, by simp [h]⟩
  · exact ⟨1, le_refl _, by simp; linear_combination h⟩

/-- **The narrowed certificate**: six boolean bits and `len + Σ_{i<5} 2^i bᵢ + 29 b₅ = 60` give
`natOf len ≤ 60` (`64 ≤ p`). -/
theorem certNat_le_60 (hF : GeneratedField.PrimeFieldElems F) (hp : 64 ≤ ringChar F)
    (bt : ℕ → F) (hb : ∀ i < 6, bt i * (bt i - 1) = 0) (len : F)
    (hc : len + ∑ i ∈ Finset.range 5, (2 : F) ^ i * bt i + 29 * bt 5 - 60 = 0) :
    natOf len ≤ 60 := by
  obtain ⟨β0, h0, e0⟩ := bool_nat (hb 0 (by norm_num))
  obtain ⟨β1, h1, e1⟩ := bool_nat (hb 1 (by norm_num))
  obtain ⟨β2, h2, e2⟩ := bool_nat (hb 2 (by norm_num))
  obtain ⟨β3, h3, e3⟩ := bool_nat (hb 3 (by norm_num))
  obtain ⟨β4, h4, e4⟩ := bool_nat (hb 4 (by norm_num))
  obtain ⟨β5, h5, e5⟩ := bool_nat (hb 5 (by norm_num))
  set s : ℕ := β0 + 2 * β1 + 4 * β2 + 8 * β3 + 16 * β4 + 29 * β5 with hs
  have hs60 : s ≤ 60 := by omega
  have hsum : ∑ i ∈ Finset.range 5, (2 : F) ^ i * bt i + 29 * bt 5 = (s : F) := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero,
      e0, e1, e2, e3, e4, e5, hs]
    push_cast; ring
  have hk := natOf_lt hF len
  have heq : ((natOf len + s : ℕ) : F) = ((60 : ℕ) : F) := by
    push_cast; rw [natOf_cast hF len, ← hsum]; linear_combination hc
  rw [CharP.natCast_eq_natCast F (ringChar F)] at heq
  rcases le_or_gt 60 (natOf len + s) with hge | hlt
  · have hdvd : ringChar F ∣ natOf len + s - 60 := (Nat.modEq_iff_dvd' hge).mp heq.symm
    have hz : natOf len + s - 60 = 0 := Nat.eq_zero_of_dvd_of_lt hdvd (by omega)
    omega
  · omega

/-- The OLD certificate value of a row with `natOf len = L`: `61 − L`. -/
def certS (L : ℕ) : ℕ := 61 - L
/-- Its bit `i`. -/
def certB (L i : ℕ) : ℕ := certS L / 2 ^ i % 2

/-- The value placed in column `c ∈ [14, 21)`: `u = b₁ b₂` at `14`, bit `c − 15` at `15..20`. -/
def fixVal (L c : ℕ) : F := if c = 14 then ((certB L 1 * certB L 2 : ℕ) : F) else ((certB L (c - 15) : ℕ) : F)

theorem certB_le (L i : ℕ) : certB L i ≤ 1 := Nat.le_of_lt_succ (Nat.mod_lt _ (by norm_num))

theorem certS_bits : ∀ S < 64, S / 1 % 2 + 2 * (S / 2 % 2) + 4 * (S / 4 % 2) + 8 * (S / 8 % 2) +
    16 * (S / 16 % 2) + 32 * (S / 32 % 2) = S := by decide

theorem certS_excl : ∀ S < 62, (S / 2 % 2) * (S / 4 % 2) * (S / 8 % 2) * (S / 16 % 2) * (S / 32 % 2) = 0 := by
  decide

end Cert

/-! ## 5. `bitFix`: the old certificate re-chosen, every other column kept -/

section Fix
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
  (δF : F) (kroots : ℕ) (b : Basis (Fin 3) F K) {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F)
  (orbit : StrictOrbitDomain F 3 h) (chals pubs : ℕ → K)

theorem widthJ8_eq : (walkChipJ8 δF kroots b hn nodes orbit chals pubs).rap.w =
    (walkChipHQK δF kroots b hn nodes orbit chals pubs).rap.w := by
  rw [walkChipJ8_width, walkChipHQK_width]

variable (Q : Fin (walkChipJ8 δF kroots b hn nodes orbit chals pubs).rap.w → F[X])

/-- The `len` column of a J-8 trace. -/
def lenPoly : F[X] := Q ⟨WChip.len, by rw [walkChipJ8_width]; decide⟩

open Classical in
/-- **`bitFix`**: columns `14..20` replaced by the interpolants (over the row set) of the OLD
certificate of the row's own `len`; every other column is `Q`'s. -/
def bitFix : Fin (walkChipHQK δF kroots b hn nodes orbit chals pubs).rap.w → F[X] := fun c =>
  if 14 ≤ (c : ℕ) ∧ (c : ℕ) < 21 then
    Lagrange.interpolate (rowNodeSet nodes) id
      (fun x => fixVal (natOf ((lenPoly δF kroots b hn nodes orbit chals pubs Q).eval x)) c)
  else Q ⟨c, by rw [widthJ8_eq]; exact c.2⟩

theorem bitFix_off (c : Fin (walkChipHQK δF kroots b hn nodes orbit chals pubs).rap.w)
    (hc : (c : ℕ) < 14 ∨ 21 ≤ (c : ℕ)) :
    bitFix δF kroots b hn nodes orbit chals pubs Q c = Q ⟨c, by rw [widthJ8_eq]; exact c.2⟩ := by
  unfold bitFix; rw [if_neg (by omega)]

theorem bitFix_on (c : Fin (walkChipHQK δF kroots b hn nodes orbit chals pubs).rap.w)
    (hc : 14 ≤ (c : ℕ) ∧ (c : ℕ) < 21) {x : F} (hx : x ∈ rowNodeSet nodes) :
    (bitFix δF kroots b hn nodes orbit chals pubs Q c).eval x =
      fixVal (natOf ((lenPoly δF kroots b hn nodes orbit chals pubs Q).eval x)) c := by
  classical
  unfold bitFix; rw [if_pos hc]
  have key := Lagrange.eval_interpolate_at_node (v := id) (s := rowNodeSet nodes)
    (r := fun x => fixVal (natOf ((lenPoly δF kroots b hn nodes orbit chals pubs Q).eval x)) c)
    (Set.injOn_id _) hx
  simpa only [id] using key

end Fix

/-! ## 6. `bitFix` of an accepted J-8 trace is accepted by `walkChipHQK` -/

section Sat
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
  (δF : F) (kroots : ℕ) (b : Basis (Fin 3) F K) {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F)
  (orbit : StrictOrbitDomain F 3 h) (chals pubs : ℕ → K)
  (Q : Fin (walkChipJ8 δF kroots b hn nodes orbit chals pubs).rap.w → F[X])

/-- The J-8 trace's row environment at a point. -/
abbrev eJ (x : F) : Env F :=
  Reify.envOfTrace Q orbit.ω x (slotVal b 25 chals) (slotVal b 25 pubs)
/-- The fixed trace's row environment at a point. -/
abbrev eX (x : F) : Env F :=
  Reify.envOfTrace (bitFix δF kroots b hn nodes orbit chals pubs Q) orbit.ω x
    (slotVal b 25 chals) (slotVal b 25 pubs)

theorem fix_agree (x : F) :
    AgreeOff (eJ δF kroots b hn nodes orbit chals pubs Q x) (eX δF kroots b hn nodes orbit chals pubs Q x) := by
  have hw := widthJ8_eq δF kroots b hn nodes orbit chals pubs
  refine ⟨fun j hj => ⟨?_, ?_⟩, rfl, rfl⟩
  · simp only [Reify.envOfTrace]
    split_ifs with h1 h2 h2
    · rw [bitFix_off δF kroots b hn nodes orbit chals pubs Q ⟨j, h2⟩ hj]
    · exact absurd (hw ▸ h1) h2
    · exact absurd (hw ▸ h2) h1
    · rfl
  · simp only [Reify.envOfTrace]
    split_ifs with h1 h2 h2
    · rw [bitFix_off δF kroots b hn nodes orbit chals pubs Q ⟨j, h2⟩ hj]
    · exact absurd (hw ▸ h1) h2
    · exact absurd (hw ▸ h2) h1
    · rfl

theorem fix_on (x : F) (hx : x ∈ rowNodeSet nodes) (c : ℕ) (hc : 14 ≤ c ∧ c < 21) :
    (eX δF kroots b hn nodes orbit chals pubs Q x).trace c =
      fixVal (natOf ((eJ δF kroots b hn nodes orbit chals pubs Q x).trace WChip.len)) c := by
  have hw : c < (walkChipHQK δF kroots b hn nodes orbit chals pubs).rap.w := by
    rw [walkChipHQK_width]; omega
  have hl : WChip.len < (walkChipJ8 δF kroots b hn nodes orbit chals pubs).rap.w := by
    rw [walkChipJ8_width]; decide
  simp only [Reify.envOfTrace, dif_pos hw, dif_pos hl]
  exact bitFix_on δF kroots b hn nodes orbit chals pubs Q ⟨c, hw⟩ hc hx

/-- **The narrowed depth bound at every point of the row set**: `natOf len ≤ 60`. -/
theorem len_le_60_at (hF : GeneratedField.PrimeFieldElems F) (hp : 64 ≤ ringChar F)
    (hsat : (walkChipJ8 δF kroots b hn nodes orbit chals pubs).rap.Satisfies Q)
    (x : F) (hx : x ∈ rowNodeSet nodes) :
    natOf ((eJ δF kroots b hn nodes orbit chals pubs Q x).trace WChip.len) ≤ 60 := by
  have hs : (expandChip (walkTemplateJ8 δF kroots) b (slotVal b 25 chals) (slotVal b 25 pubs) orbit
      (rowNodeSet nodes)).Satisfies Q := hsat
  erw [expandChip_satisfies_iff_language] at hs
  obtain ⟨hb, -, -, -⟩ := hs x hx
  have gb : ∀ j < 6, (eJ δF kroots b hn nodes orbit chals pubs Q x).trace (WChip.bit0 + j) *
      ((eJ δF kroots b hn nodes orbit chals pubs Q x).trace (WChip.bit0 + j) - 1) = 0 := by
    intro j hj
    have := hb (boolE (WChip.bt j)) (by
      show _ ∈ baseGatesJ8 kroots ++ baseHK
      simp only [baseGatesJ8, basePost, List.mem_append, List.mem_map, List.mem_range]
      exact Or.inl (Or.inr (Or.inr ⟨j, hj, rfl⟩)))
    simp only [CoeffExpr.eval, cv, boolE, WChip.bt] at this
    exact this
  have gc := hb depthJ8 (by
    show _ ∈ baseGatesJ8 kroots ++ baseHK
    simp [baseGatesJ8])
  simp only [depthJ8, CoeffExpr.eval, eval_bitSum, cv, WChip.bt] at gc
  exact certNat_le_60 hF hp (fun j => (eJ δF kroots b hn nodes orbit chals pubs Q x).trace (WChip.bit0 + j)) gb _ gc

theorem gather_eq (x : F) :
    gatherEnv b ((walkTemplateHQK δF kroots).col0 3) (eX δF kroots b hn nodes orbit chals pubs Q x) =
      gatherEnv b ((walkTemplateJ8 δF kroots).col0 3) (eJ δF kroots b hn nodes orbit chals pubs Q x) := by
  have hA := fix_agree δF kroots b hn nodes orbit chals pubs Q x
  have c1 : (walkTemplateHQK δF kroots).col0 3 = fun _ idx => 25 + 3 * idx := by
    funext k idx; simp [ChipTemplate.col0, walkTemplateHQK_baseCols]
  have c2 : (walkTemplateJ8 δF kroots).col0 3 = fun _ idx => 25 + 3 * idx := by
    funext k idx; simp [ChipTemplate.col0, walkTemplateJ8_baseCols]
  rw [c1, c2]
  unfold gatherEnv
  congr 1
  · funext idx; refine Finset.sum_congr rfl fun k _ => ?_
    exact congrArg (· • b k) (hA.1 (25 + 3 * idx + k) (by omega)).1.symm
  · funext idx; refine Finset.sum_congr rfl fun k _ => ?_
    exact congrArg (· • b k) (hA.1 (25 + 3 * idx + k) (by omega)).2.symm

/-- **`bitFix` of an accepted `walkChipJ8` trace is accepted by `walkChipHQK`.** -/
theorem walkChipJ8_bitFix_sat (hF : GeneratedField.PrimeFieldElems F) (hp : 64 ≤ ringChar F)
    (hsat : (walkChipJ8 δF kroots b hn nodes orbit chals pubs).rap.Satisfies Q) :
    (walkChipHQK δF kroots b hn nodes orbit chals pubs).rap.Satisfies
      (bitFix δF kroots b hn nodes orbit chals pubs Q) := by
  have hL := len_le_60_at δF kroots b hn nodes orbit chals pubs Q hF hp hsat
  have hs : (expandChip (walkTemplateJ8 δF kroots) b (slotVal b 25 chals) (slotVal b 25 pubs) orbit
      (rowNodeSet nodes)).Satisfies Q := hsat
  show (expandChip (walkTemplateHQK δF kroots) b (slotVal b 25 chals) (slotVal b 25 pubs) orbit
      (rowNodeSet nodes)).Satisfies (bitFix δF kroots b hn nodes orbit chals pubs Q)
  erw [expandChip_satisfies_iff_language] at hs ⊢
  intro x hx
  obtain ⟨hb, -, -, hm⟩ := hs x hx
  have hA := fix_agree δF kroots b hn nodes orbit chals pubs Q x
  have hLx := hL x hx
  obtain ⟨L, hLdef⟩ : ∃ L, L = natOf ((eJ δF kroots b hn nodes orbit chals pubs Q x).trace WChip.len) :=
    ⟨_, rfl⟩
  rw [← hLdef] at hLx
  have hon : ∀ c, 14 ≤ c ∧ c < 21 → (eX δF kroots b hn nodes orbit chals pubs Q x).trace c = fixVal L c := by
    intro c hc; rw [fix_on δF kroots b hn nodes orbit chals pubs Q x hx c hc, hLdef]
  have hu : (eX δF kroots b hn nodes orbit chals pubs Q x).trace 14 = ((certB L 1 * certB L 2 : ℕ) : F) := by
    rw [hon 14 (by omega)]; simp [fixVal]
  have hbit : ∀ i < 6, (eX δF kroots b hn nodes orbit chals pubs Q x).trace (15 + i) = ((certB L i : ℕ) : F) := by
    intro i hi; rw [hon (15 + i) (by omega)]; simp only [fixVal]; rw [if_neg (by omega)]
    congr 3; omega
  have hlen : (eX δF kroots b hn nodes orbit chals pubs Q x).trace 6 = (L : F) := by
    rw [← (hA.1 6 (by omega)).1, hLdef]; exact (natOf_cast hF _).symm
  have hS : certS L < 62 := by unfold certS; omega
  have hJ : ∀ g ∈ baseGatesJ8 (F := F) kroots ++ baseHK,
      g.eval (eJ δF kroots b hn nodes orbit chals pubs Q x) = 0 := hb
  have viaJ : ∀ g, avC g = true → g ∈ baseGatesJ8 (F := F) kroots ++ baseHK →
      g.eval (eX δF kroots b hn nodes orbit chals pubs Q x) = 0 :=
    fun g hav hmem => (avC_eval hA g hav).symm.trans (hJ g hmem)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro g hg
    have hg' : g ∈ (basePre ++ [exclOld, depthOld] ++ basePost kroots) ++ baseHK := by
      rw [← baseGates_split]; exact hg
    show g.eval (eX δF kroots b hn nodes orbit chals pubs Q x) = 0
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hg'
    rcases hg' with ((hg' | hg' | hg') | hg') | hg'
    · -- basePre
      simp only [basePre, List.mem_cons, List.not_mem_nil, or_false] at hg'
      rcases hg' with rfl | rfl | rfl | rfl
      · exact viaJ _ (by simp [avC, cv, WChip.cL]) (by simp [baseGatesJ8, basePre])
      · exact viaJ _ (by simp [avC, cv, WChip.cR]) (by simp [baseGatesJ8, basePre])
      · exact viaJ _ (by simp [avC, cv, WChip.cR, WChip.cL, WChip.e]) (by simp [baseGatesJ8, basePre])
      · have h1 := hbit 1 (by norm_num); have h2 := hbit 2 (by norm_num)
        simp only [CoeffExpr.eval, cv, WChip.bt, WChip.u, WChip.bit0]
        rw [hu, h1, h2]; push_cast; ring
    · -- exclusion
      subst hg'
      have h3 := hbit 3 (by norm_num); have h4 := hbit 4 (by norm_num); have h5 := hbit 5 (by norm_num)
      simp only [exclOld, CoeffExpr.eval, cv, WChip.bt, WChip.u, WChip.bit0]
      rw [hu, h3, h4, h5]
      have := certS_excl (certS L) hS
      have e : certB L 1 * certB L 2 * certB L 3 * certB L 4 * certB L 5 = 0 := by
        simpa [certB] using this
      have e' : ((certB L 1 * certB L 2 * certB L 3 * certB L 4 * certB L 5 : ℕ) : F) = 0 := by
        rw [e]; simp
      push_cast at e' ⊢; linear_combination e'
    · -- depth
      subst hg'
      simp only [depthOld, CoeffExpr.eval, eval_bitSum, cv, WChip.len, WChip.bit0]
      rw [hlen]
      simp only [Finset.sum_range_succ, Finset.sum_range_zero]
      rw [hbit 0 (by norm_num), hbit 1 (by norm_num), hbit 2 (by norm_num), hbit 3 (by norm_num),
        hbit 4 (by norm_num), hbit 5 (by norm_num)]
      have hsum := certS_bits (certS L) (by omega)
      have e : L + (certB L 0 + 2 * certB L 1 + 4 * certB L 2 + 8 * certB L 3 + 16 * certB L 4 +
          32 * certB L 5) = 61 := by
        simp only [certB, pow_zero, pow_one, Nat.div_one] at hsum ⊢
        norm_num at hsum ⊢
        unfold certS at hsum ⊢; omega
      have e' : ((L + (certB L 0 + 2 * certB L 1 + 4 * certB L 2 + 8 * certB L 3 + 16 * certB L 4 +
          32 * certB L 5) : ℕ) : F) = ((61 : ℕ) : F) := by rw [e]
      push_cast at e'; linear_combination e'
    · -- basePost
      simp only [basePost, List.mem_append, List.mem_map, List.mem_range] at hg'
      rcases hg' with hg' | ⟨i, hi, rfl⟩
      · exact viaJ _ (basePost_av kroots g (by simpa [basePost] using hg'))
          (by simp only [baseGatesJ8, basePost, List.mem_append]; exact Or.inl (Or.inr (Or.inl hg')))
      · have := hbit i hi
        simp only [boolE, CoeffExpr.eval, cv, WChip.bt, WChip.bit0]
        rw [this]
        rcases Nat.le_one_iff_eq_zero_or_eq_one.mp (certB_le L i) with h0 | h1
        · rw [h0]; simp
        · rw [h1]; simp
    · -- baseHK
      exact viaJ _ (baseHK_av g hg') (List.mem_append_right _ hg')
  · intro g hg; exact absurd hg (by show g ∉ ([] : List (CoeffExpr F)); simp)
  · intro g hg; exact absurd hg (by show g ∉ (([] : List Expr) ++ [] ++ []); simp)
  · intro g hg
    have hav : avM g = true := by
      rcases List.mem_append.mp hg with hg | hg
      · exact walkMixed_av δF kroots g hg
      · exact walkHQ_av δF g hg
    have key := (avM_eval hA _ g hav).symm.trans (hm g hg)
    have key2 : g.eval (gatherEnv b ((walkTemplateHQK δF kroots).col0 3)
        (eX δF kroots b hn nodes orbit chals pubs Q x)) (eX δF kroots b hn nodes orbit chals pubs Q x) = 0 := by
      rw [gather_eq δF kroots b hn nodes orbit chals pubs Q x]; exact key
    exact key2

end Sat

/-! ## 7. Binding, the row bound, and record axes `< 2^62` -/

section Rows
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
  (δF : F) (kroots : ℕ) (b : Basis (Fin 3) F K) {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F)
  (orbit : StrictOrbitDomain F 3 h) (chals pubs : ℕ → K)
  (Q : Fin (walkChipJ8 δF kroots b hn nodes orbit chals pubs).rap.w → F[X])

/-- **`bitFix` keeps the preprocessing** (the masks are columns `0..2`). -/
theorem walkChipJ8_bitFix_bind
    (hbind : (walkChipJ8 δF kroots b hn nodes orbit chals pubs).BindsPreprocessing Q) :
    (walkChipHQK δF kroots b hn nodes orbit chals pubs).BindsPreprocessing
      (bitFix δF kroots b hn nodes orbit chals pubs Q) := by
  intro j
  have hj := hbind j
  fin_cases j <;>
  · refine Eq.trans ?_ hj
    exact bitFix_off δF kroots b hn nodes orbit chals pubs Q _ (Or.inl (by
      first
      | exact (show (0 : ℕ) < 14 by norm_num)
      | exact (show (1 : ℕ) < 14 by norm_num)
      | exact (show (2 : ℕ) < 14 by norm_num)))

/-- **The narrowed bound at every walk row of the fixed trace**: `natOf len ≤ 60`. -/
theorem walkJ8_len_le_60 (hF : GeneratedField.PrimeFieldElems F) (hp : 64 ≤ ringChar F)
    (hsat : (walkChipJ8 δF kroots b hn nodes orbit chals pubs).rap.Satisfies Q) :
    ∀ j < n, natOf ((AtomWalkAW.walkEnvFA δF kroots b hn nodes orbit chals pubs
      (bitFix δF kroots b hn nodes orbit chals pubs Q) j).trace WChip.len) ≤ 60 := by
  intro j hj
  have hx : nodes ⟨j, hj⟩ ∈ rowNodeSet nodes := by
    classical
    unfold rowNodeSet; exact Finset.mem_image_of_mem _ (Finset.mem_univ _)
  have e := (fix_agree δF kroots b hn nodes orbit chals pubs Q (nodes ⟨j, hj⟩)).1 WChip.len (by decide)
  have : (AtomWalkAW.walkEnvFA δF kroots b hn nodes orbit chals pubs
      (bitFix δF kroots b hn nodes orbit chals pubs Q) j).trace WChip.len =
      (eX δF kroots b hn nodes orbit chals pubs Q (nodes ⟨j, hj⟩)).trace WChip.len := by
    simp only [AtomWalkAW.walkEnvFA, dif_pos hj]
  rw [this, ← e.1]
  exact len_le_60_at δF kroots b hn nodes orbit chals pubs Q hF hp hsat _ hx

end Rows

section Axis
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq F]
  [Fintype K] [DecidableEq K] [Fact (ringChar F).Prime] [Algebra (ZMod (ringChar F)) K]
  (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))]
  (kroots : ℕ) (b : Basis (Fin 3) F K) {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F)
  (orbit : StrictOrbitDomain F 3 h) (chals pubs : ℕ → K)
  (Q : Fin (walkChipHQK δF kroots b hn nodes orbit chals pubs).rap.w → F[X])
  (hsat : (walkChipHQK δF kroots b hn nodes orbit chals pubs).rap.Satisfies Q)
  (hbind : (walkChipHQK δF kroots b hn nodes orbit chals pubs).BindsPreprocessing Q)
  (hinj : Function.Injective nodes)
  (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω)
  (hF : GeneratedField.PrimeFieldElems F)
  (hk : 1 ≤ kroots) (hkn : kroots ≤ n) (hkp : kroots + n < ringChar F)
  (hq : 2 ^ 63 < ringChar F)

open scoped Classical in
include hsat hbind hinj hadj hF hk hkn hkp hq in
/-- **The U step, compiled: `len ≤ 60` at every row ⇒ every record axis is in `[2, 2^62)`.**  On a
`walkChipHQK`-accepted trace (any coins: the cell walk and the atom walk alike), outside the
UNCHANGED `walkEvent` (Dmax `62`), if every row's `natOf len ≤ 60`, then every record a row provides,
at axis `2·prefix + b`, has `2 ≤ axis.val < 2^62`. -/
theorem walkHQK_axis_lt
    (hlen : ∀ j < n, natOf ((AtomWalkAW.walkEnvFA δF kroots b hn nodes orbit chals pubs Q j).trace
      WChip.len) ≤ 60)
    (hout : (chals 0, chals 1) ∉ walkEvent (algebraMap F K δF)
      (walkDataOf δF kroots b hn nodes orbit chals pubs
        (restrictWalkK δF kroots b hn nodes orbit chals pubs Q))) :
    let W := walkDataOf δF kroots b hn nodes orbit chals pubs
      (restrictWalkK δF kroots b hn nodes orbit chals pubs Q)
    ∀ i, 1 ≤ i → i ≤ n → ∀ bb : Bool,
      2 ≤ (2 * (W.lbl i).2.pre + bitZ bb).val ∧ (2 * (W.lbl i).2.pre + bitZ bb).val < 2 ^ 62 := by
  intro W i hi1 hin bb
  obtain ⟨hyp, hRG, hacc⟩ := AtomWalkAW.atomWalk_W1 δF kroots b hn nodes orbit chals pubs Q hsat hbind
    hinj hadj hF hk hkn hkp hq
  have hG : ForestReconGoal (stateSep (q := ringChar F) W.X 62) W.lbl W.kroots W.h := by
    by_contra hng
    exact hout (by simp only [walkEvent, Finset.mem_filter, Finset.mem_univ, true_and]
                   exact ⟨hyp, hacc, hng⟩)
  obtain ⟨ts, hlenT, hrvt, hlab, hfan, -⟩ := hG
  haveI : NeZero (ringChar F) := ⟨by omega⟩
  have hq' : 2 ^ (62 + 1) ≤ ringChar F := by omega
  obtain ⟨u, hu, hl, -⟩ := lab_at hlab (j := i - 1) (show i - 1 < n by omega)
  rw [show i - 1 + 1 = i by omega] at hl
  obtain ⟨r, hr, hru⟩ := (mem_bfsForest ts u).mp hu
  obtain ⟨ρ, hρ1, hρk, hρ⟩ := roots_are_rows hlenT hk hlab r hr
  have hRoot : RootOK r.label.2 := by rw [hρ]; exact (hRG ρ hρ1 hρk).1
  have hfan' : ∀ v, InTree r v → v.children.length = fanout v.label.1 := fun v hv =>
    (hfan v ((mem_bfsForest ts v).mpr ⟨r, hr, hv⟩)).symm
  have hI0 : Inv W.X 62 r.label.2 r.label.2 :=
    root_inv (by omega) (F_of_rvt (hrvt r hr)).1 hRoot
  obtain ⟨-, -, -, es, -, hesl, hpre, -⟩ := tree_inv hq' hru (hrvt r hr) hfan' hI0
  rw [hl] at hesl hpre
  have hlenv : (W.lbl i).2.len.val ≤ 60 := by
    show (zq ((walkEnvF b hn nodes orbit chals pubs
      (restrictWalkK δF kroots b hn nodes orbit chals pubs Q) (i - 1)).trace WChip.len)).val ≤ 60
    unfold zq
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt (natOf_lt hF _),
      ← AtomWalkAW.walkEnvFA_trace δF kroots b hn nodes orbit chals pubs Q (i - 1) (by decide)]
    exact hlen (i - 1) (by omega)
  have hax := axisFold_lt (es.map Edge.side)
  rw [List.length_map, hesl] at hax
  have hpos := axisFold_pos (es.map Edge.side)
  have h2 : 2 ^ ((W.lbl i).2.len.val + 1) ≤ 2 ^ 61 := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hpv : (W.lbl i).2.pre.val < 2 ^ 61 := by rw [hpre]; omega
  have hb1 : bitN bb ≤ 1 := by cases bb <;> simp [bitN]
  rw [val_axis _ _ (by omega)]
  rw [← hpre] at hpos
  constructor <;> omega

end Axis

/-! ## 8. The J-8 walk: W1–W3 through `bitFix`, plus record axes `< 2^62` -/

section J8
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq F]
  [Fintype K] [DecidableEq K] [Fact (ringChar F).Prime] [Algebra (ZMod (ringChar F)) K]
  (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))]
  (kroots : ℕ) (b : Basis (Fin 3) F K) {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F)
  (orbit : StrictOrbitDomain F 3 h) (chals pubs : ℕ → K)
  (Q : Fin (walkChipJ8 δF kroots b hn nodes orbit chals pubs).rap.w → F[X])
  (hsat : (walkChipJ8 δF kroots b hn nodes orbit chals pubs).rap.Satisfies Q)
  (hbind : (walkChipJ8 δF kroots b hn nodes orbit chals pubs).BindsPreprocessing Q)
  (hinj : Function.Injective nodes)
  (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω)
  (hF : GeneratedField.PrimeFieldElems F)
  (hk : 1 ≤ kroots) (hkn : kroots ≤ n) (hkp : kroots + n < ringChar F)
  (hq : 2 ^ 63 < ringChar F)

/-- The fixed trace's row environments agree with the J-8 trace's off columns `14..20`. -/
theorem walkEnvFA_bitFix (j c : ℕ) (hc : c < 14 ∨ 21 ≤ c) :
    (AtomWalkAW.walkEnvFA δF kroots b hn nodes orbit chals pubs
      (bitFix δF kroots b hn nodes orbit chals pubs Q) j).trace c =
    (Reify.envOfTrace Q orbit.ω (if hj : j < n then nodes ⟨j, hj⟩ else nodes ⟨0, hn⟩)
      (slotVal b 25 chals) (slotVal b 25 pubs)).trace c :=
  ((fix_agree δF kroots b hn nodes orbit chals pubs Q _).1 c hc).1.symm

include hsat hbind hF in
/-- **`walkChipJ8` acceptance ⇒ `walkChipHQK` acceptance of `bitFix Q`** (both halves). -/
theorem walkChipJ8_to_HQK (hp : 64 ≤ ringChar F) :
    (walkChipHQK δF kroots b hn nodes orbit chals pubs).rap.Satisfies
        (bitFix δF kroots b hn nodes orbit chals pubs Q) ∧
      (walkChipHQK δF kroots b hn nodes orbit chals pubs).BindsPreprocessing
        (bitFix δF kroots b hn nodes orbit chals pubs Q) :=
  ⟨walkChipJ8_bitFix_sat δF kroots b hn nodes orbit chals pubs Q hF hp hsat,
    walkChipJ8_bitFix_bind δF kroots b hn nodes orbit chals pubs Q hbind⟩

open scoped Classical in
include hsat hbind hinj hadj hF hk hkn hkp hq in
/-- **Record axes of the J-8 walk are in `[2, 2^62)`** (O4 option a, the U step of step 0 compiled):
outside the unchanged `walkEvent` of the fixed trace. -/
theorem walkJ8_axis_lt
    (hout : (chals 0, chals 1) ∉ walkEvent (algebraMap F K δF)
      (walkDataOf δF kroots b hn nodes orbit chals pubs
        (restrictWalkK δF kroots b hn nodes orbit chals pubs
          (bitFix δF kroots b hn nodes orbit chals pubs Q)))) :
    let W := walkDataOf δF kroots b hn nodes orbit chals pubs
      (restrictWalkK δF kroots b hn nodes orbit chals pubs (bitFix δF kroots b hn nodes orbit chals pubs Q))
    ∀ i, 1 ≤ i → i ≤ n → ∀ bb : Bool,
      2 ≤ (2 * (W.lbl i).2.pre + bitZ bb).val ∧ (2 * (W.lbl i).2.pre + bitZ bb).val < 2 ^ 62 := by
  have hp : 64 ≤ ringChar F := by
    have : (64 : ℕ) ≤ 2 ^ 63 := by norm_num
    omega
  obtain ⟨hs, hb⟩ := walkChipJ8_to_HQK δF kroots b hn nodes orbit chals pubs Q hsat hbind hF hp
  exact walkHQK_axis_lt δF kroots b hn nodes orbit chals pubs _ hs hb hinj hadj hF hk hkn hkp hq
    (walkJ8_len_le_60 δF kroots b hn nodes orbit chals pubs Q hF hp hsat) hout

open scoped Classical in
include hsat hbind hinj hadj hF hk hkn hkp hq in
/-- **W1–W3 for the J-8 walk** (cell walk and atom walk alike: any table side `TableAccepts z tb`):
`atomWalk_records_genuine` at `bitFix Q`, at the unchanged `walkEvent`. -/
theorem walkJ8_records_genuine {z : Quad (algebraMap F K δF)} (hz : z ≠ 0)
    {tb : List (CellRow (ringChar F) (Quad (algebraMap F K δF)))}
    {vl : List (VKey (Quad (algebraMap F K δF)))} (htab : TableAccepts z tb vl)
    (hT2 : z ∉ tableBadSeeds fuelChip (tb.map (·.b0)) [])
    (hdy : z ∉ cellDyckRootSeeds fuelChip (tb.map (·.b0)))
    (hX : KeysExported tb (walkDataOf δF kroots b hn nodes orbit chals pubs
      (restrictWalkK δF kroots b hn nodes orbit chals pubs
        (bitFix δF kroots b hn nodes orbit chals pubs Q))).X)
    (hHX : ∀ j < n, ∃ c ∈ tb,
      (natOf ((AtomWalkAW.walkEnvFA δF kroots b hn nodes orbit chals pubs
          (bitFix δF kroots b hn nodes orbit chals pubs Q) j).trace WChip.idx),
        childHOf (AtomWalkAW.walkEnvFA δF kroots b hn nodes orbit chals pubs
          (bitFix δF kroots b hn nodes orbit chals pubs Q) j) false,
        childHOf (AtomWalkAW.walkEnvFA δF kroots b hn nodes orbit chals pubs
          (bitFix δF kroots b hn nodes orbit chals pubs Q) j) true) = exportRec c.b0)
    (hout : (chals 0, chals 1) ∉ walkEvent (algebraMap F K δF)
      (walkDataOf δF kroots b hn nodes orbit chals pubs
        (restrictWalkK δF kroots b hn nodes orbit chals pubs
          (bitFix δF kroots b hn nodes orbit chals pubs Q)))) :
    let W := walkDataOf δF kroots b hn nodes orbit chals pubs
      (restrictWalkK δF kroots b hn nodes orbit chals pubs (bitFix δF kroots b hn nodes orbit chals pubs Q))
    ∀ i, 1 ≤ i → i ≤ n → ∀ bb : Bool,
      ∃ (ri : ℕ) (rt nn : Noun), (W.lbl i).2.ridx = (ri : ZMod (ringChar F)) ∧
        denH (tb.map (·.b0)) (true, ri) = some rt ∧
        denH (tb.map (·.b0)) (childHOf (AtomWalkAW.walkEnvFA δF kroots b hn nodes orbit chals pubs
          (bitFix δF kroots b hn nodes orbit chals pubs Q) (i - 1)) bb) = some nn ∧
        Noun.slot (2 * (W.lbl i).2.pre + bitZ bb).val rt = some nn := by
  have hp : 64 ≤ ringChar F := by
    have : (64 : ℕ) ≤ 2 ^ 63 := by norm_num
    omega
  obtain ⟨hs, hb⟩ := walkChipJ8_to_HQK δF kroots b hn nodes orbit chals pubs Q hsat hbind hF hp
  exact AtomWalkAW.atomWalk_records_genuine δF kroots b hn nodes orbit chals pubs _ hs hb hinj hadj hF
    hk hkn hkp hq hz htab hT2 hdy hX hHX hout

end J8

end

end Nock.NockVMROM.Thm54.VclL.Handle.WalkJ8
