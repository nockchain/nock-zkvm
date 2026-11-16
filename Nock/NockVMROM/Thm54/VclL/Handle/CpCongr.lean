/-
  Nock/NockVMROM/Thm54/VclL/Handle/CpCongr.lean

* `noCP` / `cpOK C P`: a base expression reads no challenge / public; a mixed expression reads challenge
    leaves only in `C` and publics only in `P` (its base coefficients read neither);
  * `expandChip_cp_congr`: for a template without equality / extension gates whose base gates are
    `noCP` and whose mixed gates are `cpOK C P`, satisfaction transfers between challenge / public
    vectors that agree on `C` / `P`;
  * the original chips: `Cell.mixedGates` reads challenge leaves `< 33` and publics `< 4`, `WChip.mixedGates`
    the same (`cellMixed_cp`, `walkMixed_cp`); base gates read none (from `cellBase_below`,
    `walkBase_below`); hence `cellChip_cp_congr` / `walkChip_cp_congr`.  The handle leaves `33..36` and the
    handle terminals (publics `4..7`) are therefore invisible to the original chips.
  * positive control: `cpOK` flags a read of challenge leaf `33` (`cpOK_flags_33`).
-/
import Nock.NockVMROM.Thm54.VclL.Handle.MemHQ
import Nock.NockVMROM.Thm54.VclL.Handle.TeleH

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Nock.NockVMROM.Thm54.VclL.Handle.CpCongr

open Nock Nock.Reified Nock.Framework
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP Nock.NockVMROM.Thm54.VclL.Handle
open Module
open scoped Polynomial

noncomputable section

/-! ## 1. The instruments -/

section Instr
variable {F : Type} [Field F]

/-- A base expression reads no challenge and no public. -/
def noCP : CoeffExpr F → Bool
  | .const _ => true
  | .var .challenge _ => false
  | .var .publicVal _ => false
  | .var _ _ => true
  | .add a b => noCP a && noCP b
  | .sub a b => noCP a && noCP b
  | .mul a b => noCP a && noCP b
  | .neg a => noCP a
  | .pow a _ => noCP a

/-- A mixed expression reads challenge leaves only in `C`, publics only in `P`. -/
def cpOK (C P : ℕ → Bool) : MixedExpr F → Bool
  | .Var .challenge i => C i
  | .Var .publicVal i => P i
  | .Var _ _ => true
  | .Lift g => noCP g
  | .Scale g u => noCP g && cpOK C P u
  | .Const _ => true
  | .Add x y => cpOK C P x && cpOK C P y
  | .Sub x y => cpOK C P x && cpOK C P y
  | .Neg x => cpOK C P x
  | .Mul x y => cpOK C P x && cpOK C P y
  | .Pow x _ => cpOK C P x

theorem noCP_of_colsBelow {B : ℕ} : ∀ g : CoeffExpr F, colsBelow B g = true → noCP g = true
  | .const _, _ => rfl
  | .var .traceCur _, _ => rfl
  | .var .traceNext _, _ => rfl
  | .var .challenge _, h => by simp [colsBelow] at h
  | .var .publicVal _, h => by simp [colsBelow] at h
  | .add a b, h => by
      simp only [colsBelow, Bool.and_eq_true] at h
      simp only [noCP, Bool.and_eq_true]; exact ⟨noCP_of_colsBelow a h.1, noCP_of_colsBelow b h.2⟩
  | .sub a b, h => by
      simp only [colsBelow, Bool.and_eq_true] at h
      simp only [noCP, Bool.and_eq_true]; exact ⟨noCP_of_colsBelow a h.1, noCP_of_colsBelow b h.2⟩
  | .mul a b, h => by
      simp only [colsBelow, Bool.and_eq_true] at h
      simp only [noCP, Bool.and_eq_true]; exact ⟨noCP_of_colsBelow a h.1, noCP_of_colsBelow b h.2⟩
  | .neg a, h => by simp only [colsBelow] at h; exact noCP_of_colsBelow a h
  | .pow a _, h => by simp only [colsBelow] at h; exact noCP_of_colsBelow a h

theorem noCP_eval {e e' : Env F} (ht : e.trace = e'.trace) (hn : e.traceNext = e'.traceNext) :
    ∀ g : CoeffExpr F, noCP g = true → g.eval e = g.eval e'
  | .const _, _ => rfl
  | .var .traceCur i, _ => by simp [CoeffExpr.eval, ht]
  | .var .traceNext i, _ => by simp [CoeffExpr.eval, hn]
  | .var .challenge _, h => by simp [noCP] at h
  | .var .publicVal _, h => by simp [noCP] at h
  | .add a b, h => by
      simp only [noCP, Bool.and_eq_true] at h
      simp only [CoeffExpr.eval, noCP_eval ht hn a h.1, noCP_eval ht hn b h.2]
  | .sub a b, h => by
      simp only [noCP, Bool.and_eq_true] at h
      simp only [CoeffExpr.eval, noCP_eval ht hn a h.1, noCP_eval ht hn b h.2]
  | .mul a b, h => by
      simp only [noCP, Bool.and_eq_true] at h
      simp only [CoeffExpr.eval, noCP_eval ht hn a h.1, noCP_eval ht hn b h.2]
  | .neg a, h => by simp only [noCP] at h; simp only [CoeffExpr.eval, noCP_eval ht hn a h]
  | .pow a _, h => by simp only [noCP] at h; simp only [CoeffExpr.eval, noCP_eval ht hn a h]

variable {K : Type} [Field K] [Algebra F K]

theorem cpOK_eval (C P : ℕ → Bool) {eK eK' : Env K} {eF eF' : Env F} (hKt : eK.trace = eK'.trace)
    (hKn : eK.traceNext = eK'.traceNext) (hKc : ∀ i, C i = true → eK.chal i = eK'.chal i)
    (hKp : ∀ i, P i = true → eK.pub i = eK'.pub i) (ht : eF.trace = eF'.trace)
    (hn : eF.traceNext = eF'.traceNext) :
    ∀ g : MixedExpr F, cpOK C P g = true → g.eval eK eF = g.eval eK' eF'
  | .Var .traceCur i, _ => by simp [MixedExpr.eval, hKt]
  | .Var .traceNext i, _ => by simp [MixedExpr.eval, hKn]
  | .Var .challenge i, h => by simp only [MixedExpr.eval]; exact hKc i h
  | .Var .publicVal i, h => by simp only [MixedExpr.eval]; exact hKp i h
  | .Lift g, h => by simp only [cpOK] at h; simp only [MixedExpr.eval, noCP_eval ht hn g h]
  | .Scale g u, h => by
      simp only [cpOK, Bool.and_eq_true] at h
      simp only [MixedExpr.eval, noCP_eval ht hn g h.1, cpOK_eval C P hKt hKn hKc hKp ht hn u h.2]
  | .Const _, _ => rfl
  | .Add x y, h => by
      simp only [cpOK, Bool.and_eq_true] at h
      simp only [MixedExpr.eval, cpOK_eval C P hKt hKn hKc hKp ht hn x h.1,
        cpOK_eval C P hKt hKn hKc hKp ht hn y h.2]
  | .Sub x y, h => by
      simp only [cpOK, Bool.and_eq_true] at h
      simp only [MixedExpr.eval, cpOK_eval C P hKt hKn hKc hKp ht hn x h.1,
        cpOK_eval C P hKt hKn hKc hKp ht hn y h.2]
  | .Neg x, h => by
      simp only [cpOK] at h; simp only [MixedExpr.eval, cpOK_eval C P hKt hKn hKc hKp ht hn x h]
  | .Mul x y, h => by
      simp only [cpOK, Bool.and_eq_true] at h
      simp only [MixedExpr.eval, cpOK_eval C P hKt hKn hKc hKp ht hn x h.1,
        cpOK_eval C P hKt hKn hKc hKp ht hn y h.2]
  | .Pow x _, h => by
      simp only [cpOK] at h; simp only [MixedExpr.eval, cpOK_eval C P hKt hKn hKc hKp ht hn x h]

end Instr

/-! ## 2. Satisfaction transfers across agreeing challenge / public vectors -/

section Congr
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
  (b : Basis (Fin 3) F K) {h : ℕ} (orbit : StrictOrbitDomain F 3 h) (H : Finset F)

theorem expandChip_cp_congr (T : ChipTemplate F) (B : ℕ) (hBe : T.baseCols = B) (C P : ℕ → Bool)
    (hEq : T.equalityChecks = []) (hExt : T.extTransition ++ T.extDeg1 ++ T.extDeg3 = [])
    (hbase : ∀ g ∈ T.baseTransition, noCP g = true) (hmix : ∀ g ∈ T.mixedTransition, cpOK C P g = true)
    (chals pubs chals' pubs' : ℕ → K) (hc : ∀ i, C i = true → chals i = chals' i)
    (hp : ∀ i, P i = true → pubs i = pubs' i)
    (Q : Fin (expandChip T b (slotVal b B chals) (slotVal b B pubs) orbit H).w → F[X])
    (hsat : (expandChip T b (slotVal b B chals) (slotVal b B pubs) orbit H).Satisfies Q) :
    (expandChip T b (slotVal b B chals') (slotVal b B pubs') orbit H).Satisfies Q := by
  erw [expandChip_satisfies_iff_language] at hsat ⊢
  intro x hx
  obtain ⟨hb, -, -, hm⟩ := hsat x hx
  refine ⟨fun g hg => ?_, by rw [hEq]; simp, by rw [hExt]; simp, fun g hg => ?_⟩
  · rw [← hb g hg]
    refine noCP_eval ?_ ?_ g (hbase g hg) <;> rfl
  · rw [← hm g hg]
    refine cpOK_eval C P ?_ ?_ (fun i hi => ?_) (fun i hi => ?_) ?_ ?_ g (hmix g hg)
    · rfl
    · rfl
    · rw [TeleH.gather_chal_T b T B hBe _ chals' rfl, TeleH.gather_chal_T b T B hBe _ chals rfl]
      exact (hc i hi).symm
    · rw [TeleH.gather_pub_T b T B hBe _ pubs' rfl, TeleH.gather_pub_T b T B hBe _ pubs rfl]
      exact (hp i hi).symm
    · rfl
    · rfl

end Congr

/-! ## 3. The original memory chips -/

section Orig
variable {F : Type} [Field F]

/-- The original chips' challenge leaves (`< 33`) and publics (`< 4`). -/
def cLow (i : ℕ) : Bool := decide (i < 33)
def pLow (i : ℕ) : Bool := decide (i < 4)

theorem cellMixed_cp (δF : F) : ∀ g ∈ Cell.mixedGates δF, cpOK cLow pLow g = true := by
  have hall : (Cell.mixedGates δF).all (cpOK cLow pLow) = true := by
    simp [Cell.mixedGates, Cell.qEqs, Cell.consEqs, Cell.atomEqs, Cell.vKeyP, Cell.vKeyL,
      Cell.vKeyR, Cell.xKey, Cell.xKeyS, Cell.vTerm, Cell.xTerm, QE.gates, QE.var, QE.next, QE.chal,
      QE.pub, QE.base, QE.mk2, QE.zero, QE.one, QE.add, QE.sub, QE.mul, QE.scale, QE.rlc, QE.gpow,
      QFP.var, QFP.next, QFP.entries, QFP.sub, QFP.add, QFP.scale, QFP.gates, den, zQ, rQ,
      cpOK, noCP, cLow, pLow, List.zipIdx, Cell.pR, Cell.lR, Cell.rR, Cell.vProvInv, Cell.consLInv,
      Cell.consRInv, Cell.xProvInv, Cell.xProvInv1, Cell.vAcc, Cell.xAcc, Cell.isF, Cell.isL,
      Cell.idx, Cell.idL, Cell.idR, Cell.wL, Cell.wR, Cell.aL, Cell.aR, Cell.lo, Cell.hi, Cell.loL,
      Cell.hiL, Cell.loR, Cell.hiR, Cell.mv, Cell.mx, Cell.mx1]
  intro g hg
  exact List.all_eq_true.mp hall g hg

theorem walkMixed_cp (δF : F) (kroots : ℕ) : ∀ g ∈ WChip.mixedGates δF kroots, cpOK cLow pLow g = true := by
  have hall : (WChip.mixedGates δF kroots).all (cpOK cLow pLow) = true := by
    simp [WChip.mixedGates, WChip.walkGates, WChip.qEqs, WChip.xKey, WChip.recL, WChip.recR,
      WChip.pTerm, WChip.curW, WChip.childLW, WChip.childRW, WChip.afoW, WChip.ccW, WChip.αk,
      WChip.αE, WChip.γE, WChip.rlcW, WChip.sumME, WChip.vecAt, List.ofFn_succ, QE.gates, QE.var,
      QE.next, QE.chal, QE.pub, QE.base, QE.zero, QE.one, QE.add, QE.sub, QE.mul, QE.scale,
      QE.rlc, QE.gpow, QFP.var, QFP.next, QFP.entries, QFP.sub, QFP.add, QFP.scale, QFP.gates, den,
      rQ, cpOK, noCP, cLow, pLow, List.zipIdx, WChip.pR, WChip.lR, WChip.rR, WChip.rootR, WChip.lnR,
      WChip.cntR, WChip.accR, WChip.xInv, WChip.pInvL, WChip.pInvR, WChip.xAcc, WChip.pAcc,
      WChip.isF, WChip.isL, WChip.rM, WChip.idx, WChip.pre, WChip.ridx, WChip.len, WChip.cL,
      WChip.cR, WChip.e, WChip.mL, WChip.mR]
  intro g hg
  exact List.all_eq_true.mp hall g hg

/-- Positive control: a read of challenge leaf `33` (a handle coin) is flagged. -/
theorem cpOK_flags_33 : cpOK (F := F) cLow pLow (.Var .challenge 33) = false := rfl

/-- Positive control: a read of public `4` (a handle terminal) is flagged. -/
theorem cpOK_flags_pub4 : cpOK (F := F) cLow pLow (.Var .publicVal 4) = false := rfl

end Orig

section Chips
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
  (δF : F) (b : Basis (Fin 3) F K) {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F)
  (orbit : StrictOrbitDomain F 3 h) (chals pubs chals' pubs' : ℕ → K)

/-- **The original cell chip sees only challenge leaves `< 33` and publics `< 4`.** -/
theorem cellChip_cp_congr (hc : ∀ i < 33, chals i = chals' i) (hp : ∀ i < 4, pubs i = pubs' i)
    (Q : Fin (cellChip δF b hn nodes orbit chals pubs).rap.w → F[X])
    (hsat : (cellChip δF b hn nodes orbit chals pubs).rap.Satisfies Q) :
    (cellChip δF b hn nodes orbit chals' pubs').rap.Satisfies Q :=
  expandChip_cp_congr b orbit _ (cellTemplate δF) 129 (cellTemplate_baseCols δF) cLow pLow rfl rfl
    (fun g hg => noCP_of_colsBelow g (cellBase_below g hg)) (cellMixed_cp δF) chals pubs chals' pubs'
    (fun i hi => hc i (by simpa [cLow] using hi)) (fun i hi => hp i (by simpa [pLow] using hi)) Q hsat

/-- **The original walk chip sees only challenge leaves `< 33` and publics `< 4`.** -/
theorem walkChip_cp_congr (kroots : ℕ) (hc : ∀ i < 33, chals i = chals' i) (hp : ∀ i < 4, pubs i = pubs' i)
    (Q : Fin (walkChip δF kroots b hn nodes orbit chals pubs).rap.w → F[X])
    (hsat : (walkChip δF kroots b hn nodes orbit chals pubs).rap.Satisfies Q) :
    (walkChip δF kroots b hn nodes orbit chals' pubs').rap.Satisfies Q :=
  expandChip_cp_congr b orbit _ (walkTemplate δF kroots) 21 (walkTemplate_baseCols δF kroots) cLow pLow rfl rfl
    (fun g hg => noCP_of_colsBelow g (walkBase_below kroots g hg)) (walkMixed_cp δF kroots)
    chals pubs chals' pubs'
    (fun i hi => hc i (by simpa [cLow] using hi)) (fun i hi => hp i (by simpa [pLow] using hi)) Q hsat

end Chips

end

end Nock.NockVMROM.Thm54.VclL.Handle.CpCongr
