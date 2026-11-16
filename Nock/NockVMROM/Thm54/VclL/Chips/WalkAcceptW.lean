/-
  Nock/NockVMROM/Thm54/VclL/Chips/WalkAcceptW.lean

  Nothing is re-derived: the
  closed forms, the seed identity and the bridge are trunk's.
-/
import Nock.NockVMROM.Thm54.VclL.Chips.RowBridgeW

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP

open Nock.Reified
open Nock.Framework
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.CoordinateBasis
open Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler
open Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.StrictExtension
open Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.VclL
open Nock.ComputeTable (FP)
open Module
open scoped Polynomial

noncomputable section

/-! ## 1. Evaluating the in-gate RLCs -/

section Eval
variable {F K : Type} [Field F] [Field K] [Algebra F K]

theorem sumME_eval (eK : Env K) (eF : Env F) (l : List (MixedExpr F)) :
    (WChip.sumME l).eval eK eF = (l.map fun x => x.eval eK eF).sum := by
  induction l with
  | nil => simp [WChip.sumME, MixedExpr.eval]
  | cons a t ih => simp [WChip.sumME, MixedExpr.eval, ih]

theorem rlcW_eval (eK : Env K) (eF : Env F) (v : Fin 15 → MixedExpr F) :
    (WChip.rlcW v).eval eK eF = ∑ c : Fin 15, eK.chal 1 ^ (c : ℕ) * (v c).eval eK eF := by
  rw [WChip.rlcW, sumME_eval, List.map_ofFn, List.sum_ofFn]
  rfl

variable [DecidableEq F] [Fintype K] [DecidableEq K] [Fact (ringChar F).Prime]
  [Algebra (ZMod (ringChar F)) K] (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))]
  (hF : GeneratedField.PrimeFieldElems F)
include hF

theorem algZ (x : F) :
    algebraMap (ZMod (ringChar F)) K (zq x) = algebraMap F K x := by
  rw [zq, map_natCast, ← map_natCast (algebraMap F K), natOf_cast hF]

/-- A "view" of a row: `k`-leaves read `eK'`'s trace, `bc` leaves read `eF'`'s trace. -/
structure View (k : VarKind) (bc : ℕ → CoeffExpr F) (eK eK' : Env K) (eF eF' : Env F) : Prop where
  kv : ∀ r, (MixedExpr.Var k r : MixedExpr F).eval eK eF = eK'.trace r
  bv : ∀ j, (bc j).eval eF = eF'.trace j

omit hF in
theorem view_cur (eK : Env K) (eF : Env F) : View .traceCur cv eK eK eF eF :=
  ⟨fun _ => rfl, fun _ => rfl⟩

theorem vecAt_enc {k : VarKind} {bc : ℕ → CoeffExpr F} {eK eK' : Env K} {eF eF' : Env F}
    (V : View k bc eK eK' eF eF') (nodeR : ℕ) (preE lenE : CoeffExpr F)
    (d : WalkVCL.DT (ringChar F) (Quad (algebraMap F K δF))) (s : WalkVCL.St)
    (hn : d.node = (QFP.var nodeR).ev δF eK' eF') (hroot : d.root = (QFP.var WChip.rootR).ev δF eK' eF')
    (hpre : algebraMap (ZMod (ringChar F)) K d.pre = algebraMap F K (preE.eval eF))
    (hridx : d.ridx = zq (eF'.trace WChip.ridx))
    (hlen : algebraMap (ZMod (ringChar F)) K d.len = algebraMap F K (lenE.eval eF)) :
    ∀ c : Fin 15, (WChip.vecAt k bc nodeR preE lenE c).eval eK eF =
      WalkVCL.enc (algebraMap F K δF) ((s, d) : WalkVCL.LT (ringChar F) _) c := by
  intro c
  fin_cases c <;>
    simp [WChip.vecAt, WalkVCL.enc, MixedExpr.eval, V.kv, V.bv, hn, hroot, hpre, hridx, hlen,
      QFP.ev, QFP.var, QE.ev, QE.var, Quad.re_mk, Quad.im_mk, algZ hF, map_ofNat]

theorem cur_row {k : VarKind} {bc : ℕ → CoeffExpr F} {eK eK' : Env K} {eF eF' : Env F}
    (V : View k bc eK eK' eF eF') :
    (WChip.curW k bc).eval eK eF =
      Nock.Walk.rlc (eK.chal 1) (WalkVCL.enc (algebraMap F K δF) (lblRow δF eK' eF')) := by
  rw [WChip.curW, rlcW_eval]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [vecAt_enc δF hF V WChip.pR _ _ (lblRow δF eK' eF').2 (lblRow δF eK' eF').1 rfl rfl
    (by simp [lblRow, V.bv, algZ hF]) rfl (by simp [lblRow, V.bv, algZ hF])]

/-- The child at side `b` of a row read through a view. -/
abbrev childLbl (eK' : Env K) (eF' : Env F) (b : Bool) :
    WalkVCL.LT (ringChar F) (Quad (algebraMap F K δF)) :=
  ((false, false), childDT (keyRow δF eK' eF') b (lblRow δF eK' eF').2)

theorem childL_row {k : VarKind} {bc : ℕ → CoeffExpr F} {eK eK' : Env K} {eF eF' : Env F}
    (V : View k bc eK eK' eF eF') :
    (WChip.childLW k bc).eval eK eF =
      Nock.Walk.rlc (eK.chal 1) (WalkVCL.enc (algebraMap F K δF) (childLbl δF eK' eF' false)) := by
  rw [WChip.childLW, rlcW_eval]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [vecAt_enc δF hF V WChip.lR _ _ (childDT (keyRow δF eK' eF') false (lblRow δF eK' eF').2)
    (false, false) (by simp [childDT, WalkVCL.tgt, WalkVCL.keyEdge, childOf, keyRow]) rfl
    (by simp [childDT, lblRow, WalkVCL.bitZ, CoeffExpr.eval, V.bv, algZ hF, map_ofNat]) rfl
    (by simp [childDT, lblRow, CoeffExpr.eval, V.bv, algZ hF])]

theorem childR_row {k : VarKind} {bc : ℕ → CoeffExpr F} {eK eK' : Env K} {eF eF' : Env F}
    (V : View k bc eK eK' eF eF') :
    (WChip.childRW k bc).eval eK eF =
      Nock.Walk.rlc (eK.chal 1) (WalkVCL.enc (algebraMap F K δF) (childLbl δF eK' eF' true)) := by
  rw [WChip.childRW, rlcW_eval]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [vecAt_enc δF hF V WChip.rR _ _ (childDT (keyRow δF eK' eF') true (lblRow δF eK' eF').2)
    (false, false) (by simp [childDT, WalkVCL.tgt, WalkVCL.keyEdge, childOf, keyRow]) rfl
    (by simp [childDT, lblRow, WalkVCL.bitZ, CoeffExpr.eval, V.bv, algZ hF, map_ofNat]) rfl
    (by simp [childDT, lblRow, CoeffExpr.eval, V.bv, algZ hF])]

omit hF in
theorem sum_Icc_one_two {M : Type} [AddCommMonoid M] (f : ℕ → M) :
    ∑ l ∈ Finset.Icc 1 2, f l = f 1 + f 2 := by
  rw [Finset.sum_Icc_succ_top (by norm_num), Finset.Icc_self, Finset.sum_singleton]

/-- `α^{fanout}` and `cc` at a row whose state bits are boolean and `e = cL·cR`. -/
theorem afo_cc_row {k : VarKind} {bc : ℕ → CoeffExpr F} {eK eK' : Env K} {eF eF' : Env F}
    (V : View k bc eK eK' eF eF')
    (bL : eF'.trace WChip.cL = 0 ∨ eF'.trace WChip.cL = 1)
    (bR : eF'.trace WChip.cR = 0 ∨ eF'.trace WChip.cR = 1)
    (he : eF'.trace WChip.e = eF'.trace WChip.cL * eF'.trace WChip.cR) :
    (WChip.afoW bc).eval eK eF = eK.chal 0 ^ WalkVCL.fanout (lblRow δF eK' eF').1 ∧
      (WChip.ccW k bc).eval eK eF =
        ∑ l ∈ Finset.Icc 1 (WalkVCL.fanout (lblRow δF eK' eF').1), eK.chal 0 ^ l *
          Nock.Walk.rlc (eK.chal 1) (WalkVCL.enc (algebraMap F K δF)
            (childLbl δF eK' eF' (sideOf (lblRow δF eK' eF').1 l))) := by
  have hL := childL_row δF hF V
  have hR := childR_row δF hF V
  simp only [WChip.afoW, WChip.ccW, WChip.αE, MixedExpr.eval, CoeffExpr.eval, V.bv, hL, hR, he]
  refine ⟨?_, ?_⟩ <;> rcases bL with hl | hl <;> rcases bR with hr | hr <;>
    simp [lblRow, WalkVCL.fanout, sideOf, hl, hr, sum_Icc_one_two] <;> ring

end Eval

/-! ## 2. The in-gate walk of an accepted trace -/

section Accept
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq F]
  [Fintype K] [DecidableEq K] [Fact (ringChar F).Prime] [Algebra (ZMod (ringChar F)) K]
  (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))]
  (kroots : ℕ) (b : Basis (Fin 3) F K) {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F)
  (orbit : StrictOrbitDomain F 3 h) (chals pubs : ℕ → K)
  (Q : Fin (walkChip δF kroots b hn nodes orbit chals pubs).rap.w → F[X])
  (hsat : (walkChip δF kroots b hn nodes orbit chals pubs).rap.Satisfies Q)
  (hbind : (walkChip δF kroots b hn nodes orbit chals pubs).BindsPreprocessing Q)
  (hinj : Function.Injective nodes)
  (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω)
  (hF : GeneratedField.PrimeFieldElems F)

theorem walkK_chal (j c : ℕ) : (walkEnvK δF kroots b hn nodes orbit chals pubs Q j).chal c = chals c :=
  gather_chal_walk δF kroots b chals _ rfl c

include hadj in
theorem view_next (j : ℕ) (hj : j + 1 < n) :
    View .traceNext nv (walkEnvK δF kroots b hn nodes orbit chals pubs Q j)
      (walkEnvK δF kroots b hn nodes orbit chals pubs Q (j + 1))
      (walkEnvF b hn nodes orbit chals pubs Q j) (walkEnvF b hn nodes orbit chals pubs Q (j + 1)) :=
  ⟨fun r => walkK_traceNext δF kroots b hn nodes orbit chals pubs Q hadj j hj r,
    fun r => walk_traceNext δF kroots b hn nodes orbit chals pubs Q hadj j hj r⟩

include hsat hF

/-- Booleanity of the state bits and `e = cL·cR` at a row. -/
theorem walk_state_bits (j : ℕ) (hj : j < n) :
    ((walkEnvF b hn nodes orbit chals pubs Q j).trace WChip.cL = 0 ∨
        (walkEnvF b hn nodes orbit chals pubs Q j).trace WChip.cL = 1) ∧
      ((walkEnvF b hn nodes orbit chals pubs Q j).trace WChip.cR = 0 ∨
        (walkEnvF b hn nodes orbit chals pubs Q j).trace WChip.cR = 1) ∧
      (walkEnvF b hn nodes orbit chals pubs Q j).trace WChip.e =
        (walkEnvF b hn nodes orbit chals pubs Q j).trace WChip.cL *
          (walkEnvF b hn nodes orbit chals pubs Q j).trace WChip.cR := by
  have hb := (walk_gates δF kroots b hn nodes orbit chals pubs Q hsat j hj).1
  have gL := hb (boolE (cv WChip.cL)) (by simp [WChip.baseGates])
  have gR := hb (boolE (cv WChip.cR)) (by simp [WChip.baseGates])
  have gE := hb (.sub (cv WChip.e) (.mul (cv WChip.cL) (cv WChip.cR))) (by simp [WChip.baseGates])
  simp only [CoeffExpr.eval] at gL gR gE
  exact ⟨bool_val gL, bool_val gR, sub_eq_zero.mp gE⟩

include hbind hinj hadj

theorem walk_accepts_of_chip (hk : 1 ≤ kroots) (hkn : kroots ≤ n) :
    let W := walkDataOf δF kroots b hn nodes orbit chals pubs Q
    ∃ ln count acc : ℕ → K,
      Nock.Walk.WalkSat (fun i => Nock.Walk.rlc (chals 1) (WalkVCL.enc (algebraMap F K δF) (W.lbl i)))
        (fun i l => Nock.Walk.rlc (chals 1) (WalkVCL.enc (algebraMap F K δF) (W.clab i l))) W.fo
        ln count acc (chals 0)
        (∑ i ∈ Finset.Icc 1 W.kroots,
          Nock.Walk.rlc (chals 1) (WalkVCL.enc (algebraMap F K δF) (W.lbl i)) * chals 0 ^ i)
        (chals 0 ^ W.kroots) W.h ∧ acc W.h = 0 := by
  intro W
  set eF := walkEnvF b hn nodes orbit chals pubs Q with heF
  set eK := walkEnvK δF kroots b hn nodes orbit chals pubs Q with heK
  have hch : ∀ j c, (eK j).chal c = chals c := walkK_chal δF kroots b hn nodes orbit chals pubs Q
  let cur : ℕ → K := fun i => Nock.Walk.rlc (chals 1) (WalkVCL.enc (algebraMap F K δF) (W.lbl i))
  let chld : ℕ → ℕ → K := fun i l => Nock.Walk.rlc (chals 1) (WalkVCL.enc (algebraMap F K δF) (W.clab i l))
  let ln : ℕ → K := fun i => (eK (i - 1)).trace WChip.lnR
  let cnt : ℕ → K := fun i => (eK (i - 1)).trace WChip.cntR
  let acc : ℕ → K := fun i => (eK (i - 1)).trace WChip.accR
  -- per-row facts
  have gates := fun j (hj : j < n) => walk_gates δF kroots b hn nodes orbit chals pubs Q hsat j hj
  have masks := fun j (hj : j < n) => walk_masks δF kroots b hn nodes orbit chals pubs Q hbind hinj j hj
  have bits := fun j (hj : j < n) => walk_state_bits δF kroots b hn nodes orbit chals pubs Q hsat hF j hj
  -- the current-row afo / cc and the next-row ones
  have ccC : ∀ j (hj : j < n), (WChip.afoW cv).eval (eK j) (eF j) = chals 0 ^ W.fo (j + 1) ∧
      (WChip.ccW .traceCur cv).eval (eK j) (eF j) =
        ∑ l ∈ Finset.Icc 1 (W.fo (j + 1)), chals 0 ^ l * chld (j + 1) l := by
    intro j hj
    obtain ⟨bL, bR, he⟩ := bits j hj
    have := afo_cc_row δF hF (view_cur (eK j) (eF j)) bL bR he
    rw [hch, hch] at this
    simpa [W, walkDataOf, chld, cur] using this
  have ccN : ∀ j (hj : j + 1 < n), (WChip.afoW nv).eval (eK j) (eF j) = chals 0 ^ W.fo (j + 2) ∧
      (WChip.ccW .traceNext nv).eval (eK j) (eF j) =
        ∑ l ∈ Finset.Icc 1 (W.fo (j + 2)), chals 0 ^ l * chld (j + 2) l := by
    intro j hj
    obtain ⟨bL, bR, he⟩ := bits (j + 1) hj
    have := afo_cc_row δF hF (view_next δF kroots b hn nodes orbit chals pubs Q hadj j hj) bL bR he
    rw [hch, hch] at this
    simpa [W, walkDataOf, chld, cur] using this
  have curN : ∀ j (hj : j + 1 < n), (WChip.curW .traceNext nv).eval (eK j) (eF j) = cur (j + 2) := by
    intro j hj
    have := cur_row δF hF (view_next δF kroots b hn nodes orbit chals pubs Q hadj j hj)
    rw [hch] at this
    simpa [W, walkDataOf, cur] using this
  have hw : Nock.Walk.WalkSatInGate cur chld W.fo ln cnt acc (chals 0) (chals 0 ^ kroots) kroots n := by
    refine ⟨hn, hk, hkn, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · -- ln 1 = α
      obtain ⟨-, gw, -⟩ := gates 0 hn
      have g := gw _ (by simp [WChip.walkGates] : (MixedExpr.Scale (cv WChip.isF)
        (.Sub (WChip.vC WChip.lnR) WChip.αE) : MixedExpr F) ∈ WChip.walkGates kroots)
      have hm := (masks 0 hn).1
      simp only [MixedExpr.eval, CoeffExpr.eval, cv, WChip.αE] at g
      rw [hm, if_pos rfl, map_one, one_mul, hch] at g
      exact sub_eq_zero.mp g
    · intro i hi1 hin
      obtain ⟨-, gw, -⟩ := gates (i - 1) (by omega)
      have g := gw _ (by simp [WChip.walkGates] : (MixedExpr.Scale (notE (cv WChip.isL))
        (.Sub (WChip.vN WChip.lnR) (.Mul WChip.αE (WChip.vC WChip.lnR))) : MixedExpr F) ∈
          WChip.walkGates kroots)
      have hm := (masks (i - 1) (by omega)).2.1
      have hnx := walkK_traceNext δF kroots b hn nodes orbit chals pubs Q hadj (i - 1) (by omega)
      simp only [MixedExpr.eval, CoeffExpr.eval, cv, notE, WChip.αE, hnx] at g
      rw [hm, if_neg (by omega), sub_zero, map_one, one_mul, hch, show i - 1 + 1 = i by omega] at g
      show (eK (i + 1 - 1)).trace WChip.lnR = chals 0 * (eK (i - 1)).trace WChip.lnR
      rw [show i + 1 - 1 = i by omega]; exact sub_eq_zero.mp g
    · obtain ⟨-, gw, -⟩ := gates 0 hn
      have g := gw _ (by simp [WChip.walkGates] : (MixedExpr.Scale (cv WChip.isF)
        (.Sub (WChip.vC WChip.cntR) (.Mul (WChip.αk kroots) (WChip.afoW cv))) : MixedExpr F) ∈
          WChip.walkGates kroots)
      have hm := (masks 0 hn).1
      have hc := (ccC 0 hn).1
      simp only [MixedExpr.eval, CoeffExpr.eval, cv, WChip.αk, WChip.αE] at g
      rw [hm, if_pos rfl, map_one, one_mul, hch, hc] at g
      exact sub_eq_zero.mp g
    · intro i hi1 hin
      obtain ⟨-, gw, -⟩ := gates (i - 1) (by omega)
      have g := gw _ (by simp [WChip.walkGates] : (MixedExpr.Scale (notE (cv WChip.isL))
        (.Sub (WChip.vN WChip.cntR) (.Mul (WChip.vC WChip.cntR) (WChip.afoW nv))) : MixedExpr F) ∈
          WChip.walkGates kroots)
      have hm := (masks (i - 1) (by omega)).2.1
      have hnx := walkK_traceNext δF kroots b hn nodes orbit chals pubs Q hadj (i - 1) (by omega)
      have hc := (ccN (i - 1) (by omega)).1
      simp only [MixedExpr.eval, CoeffExpr.eval, cv, notE, hnx] at g
      rw [hm, if_neg (by omega), sub_zero, map_one, one_mul, hc, show i - 1 + 1 = i by omega,
        show i - 1 + 2 = i + 1 by omega] at g
      show (eK (i + 1 - 1)).trace WChip.cntR = (eK (i - 1)).trace WChip.cntR * chals 0 ^ W.fo (i + 1)
      rw [show i + 1 - 1 = i by omega]; exact sub_eq_zero.mp g
    · obtain ⟨-, gw, -⟩ := gates 0 hn
      have g := gw _ (by simp [WChip.walkGates] : (MixedExpr.Scale (cv WChip.isF)
        (.Sub (WChip.vC WChip.accR) (.Mul (WChip.αk kroots) (WChip.ccW .traceCur cv))) :
          MixedExpr F) ∈ WChip.walkGates kroots)
      have hm := (masks 0 hn).1
      have hc := (ccC 0 hn).2
      simp only [MixedExpr.eval, CoeffExpr.eval, cv, WChip.αk, WChip.αE] at g
      rw [hm, if_pos rfl, map_one, one_mul, hch, hc] at g
      show (eK (1 - 1)).trace WChip.accR = _
      rw [sub_eq_zero.mp g, Finset.mul_sum]
      exact Finset.sum_congr rfl fun l _ => by ring
    · intro i hi1 hin
      obtain ⟨-, gw, -⟩ := gates (i - 1) (by omega)
      have g := gw _ (by simp [WChip.walkGates] : (MixedExpr.Scale (notE (cv WChip.isL))
        (.Sub (.Add (.Scale (notE (nv WChip.rM)) (.Mul (WChip.vN WChip.lnR)
            (WChip.curW .traceNext nv))) (.Sub (WChip.vN WChip.accR) (WChip.vC WChip.accR)))
          (.Mul (WChip.vC WChip.cntR) (WChip.ccW .traceNext nv))) : MixedExpr F) ∈
            WChip.walkGates kroots)
      have hm := (masks (i - 1) (by omega)).2.1
      have hr := (masks i hin).2.2
      have hnx := walkK_traceNext δF kroots b hn nodes orbit chals pubs Q hadj (i - 1) (by omega)
      have hnxF := walk_traceNext δF kroots b hn nodes orbit chals pubs Q hadj (i - 1) (by omega)
      have hc := (ccN (i - 1) (by omega)).2
      have hcu := curN (i - 1) (by omega)
      simp only [MixedExpr.eval, CoeffExpr.eval, cv, nv, notE, hnx, hnxF] at g
      rw [hm, if_neg (by omega), sub_zero, map_one, one_mul, hc, hcu, show i - 1 + 1 = i by omega,
        show i - 1 + 2 = i + 1 by omega, hr] at g
      show Nock.Walk.deqCoeff kroots (i + 1) * (eK (i + 1 - 1)).trace WChip.lnR * cur (i + 1) +
          (eK (i + 1 - 1)).trace WChip.accR - (eK (i - 1)).trace WChip.accR = _
      rw [show i + 1 - 1 = i by omega]
      have hdq : Nock.Walk.deqCoeff (K := K) kroots (i + 1) =
          algebraMap F K (1 - if i < kroots then 1 else 0) := by
        unfold Nock.Walk.deqCoeff Nock.Walk.rootMask
        by_cases hik : i < kroots
        · rw [if_pos (by omega), if_pos hik]; simp
        · rw [if_neg (by omega), if_neg hik]; simp
      have hs : ∑ l ∈ Finset.Icc 1 (W.fo (i + 1)), chals 0 ^ l * (eK (i - 1)).trace WChip.cntR *
          chld (i + 1) l = ∑ l ∈ Finset.Icc 1 (W.fo (i + 1)),
            (eK (i - 1)).trace WChip.cntR * (chals 0 ^ l * chld (i + 1) l) :=
        Finset.sum_congr rfl fun l _ => by ring
      rw [hdq, hs, ← Finset.mul_sum]; linear_combination g
  obtain ⟨acc', hws, hagree⟩ := hw.exists_walkSat_agree_ge
  refine ⟨ln, cnt, acc', ?_, ?_⟩
  · rw [Nock.Walk.nodeListP_eval] at hws
    exact hws
  · show acc' n = 0
    rw [← hagree n hn le_rfl hkn]
    obtain ⟨-, gw, -⟩ := gates (n - 1) (by omega)
    have g := gw _ (by simp [WChip.walkGates] : (MixedExpr.Scale (cv WChip.isL)
      (WChip.vC WChip.accR) : MixedExpr F) ∈ WChip.walkGates kroots)
    have hm := (masks (n - 1) (by omega)).2.1
    simp only [MixedExpr.eval, CoeffExpr.eval, cv] at g
    rw [hm, if_pos (by omega), map_one, one_mul] at g
    exact g

open scoped Classical in
theorem records_genuine_of_chip (hk : 1 ≤ kroots) (hkn : kroots ≤ n) (hkp : kroots + n < ringChar F)
    (hq : 2 ^ 63 < ringChar F) {z : Quad (algebraMap F K δF)} (hz : z ≠ 0)
    {tb : List (CellRow (ringChar F) (Quad (algebraMap F K δF)))}
    {vl : List (VKey (Quad (algebraMap F K δF)))} (htab : TableAccepts z tb vl)
    (hT2 : z ∉ tableBadSeeds fuelChip (tb.map (·.b0)) [])
    (hdy : z ∉ cellDyckRootSeeds fuelChip (tb.map (·.b0)))
    (hX : WalkVCL.KeysExported tb (walkDataOf δF kroots b hn nodes orbit chals pubs Q).X)
    (hout : (chals 0, chals 1) ∉
      WalkVCL.walkEvent (algebraMap F K δF) (walkDataOf δF kroots b hn nodes orbit chals pubs Q)) :
    WalkVCL.AllRecordsGenuine z tb (walkDataOf δF kroots b hn nodes orbit chals pubs Q).X
      (walkDataOf δF kroots b hn nodes orbit chals pubs Q).lbl n :=
  WalkVCL.records_outside_summand (algebraMap F K δF) hq hz htab hT2 hdy _ hX
    (walkHyps_of_chip δF kroots b hn nodes orbit chals pubs Q hsat hbind hinj hadj hF hk hkn hkp
      (by omega))
    (rootGate_of_chip δF kroots b hn nodes orbit chals pubs Q hsat hbind hinj hF hkn (by omega))
    (walk_accepts_of_chip δF kroots b hn nodes orbit chals pubs Q hsat hbind hinj hadj hF hk hkn)
    hout

end Accept

end

end Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
