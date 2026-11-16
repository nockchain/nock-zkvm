/-
  Nock/NockVMROM/Thm54/VclL/Handle/WalkTraceHQ.lean

  **`walkTraceHQ`, the honest 166-column `𝕂′` walk twin trace, and
  `walkChipHQ_accepts_honest`** — `walkChipHQ` is satisfiable under exactly the side conditions of
  `walkChipH_accepts_honest` read at `𝕂′`.  Additive (the `𝕂′` copy of `WalkTraceH`).

  New columns: `kL vL kR vR` at `21..24`; the ten `𝕂`-roles `37..46` (Re / Im of the export inverse,
  the two provide inverses, the two accumulators) at columns `136..165`.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.WalkTraceH
import Nock.NockVMROM.Thm54.VclL.Handle.CellTraceHQ

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Nock.NockVMROM.Thm54.VclL.Handle

open Nock Nock.Reified Nock.Framework
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Module
open scoped Polynomial

noncomputable section

namespace QGates

section
variable {F K : Type} [Field F] [Field K] [Algebra F K] [Fintype K] (δF : F)
  [Fact (¬ IsSquare (algebraMap F K δF))]

/-- The `𝕂′` value of `K`-roles `r`, `r + 1`. -/
abbrev qv (eK : Env K) (r : ℕ) : Quad (algebraMap F K δF) := Quad.mk _ (eK.trace r) (eK.trace (r + 1))
abbrev qn (eK : Env K) (r : ℕ) : Quad (algebraMap F K δF) := Quad.mk _ (eK.traceNext r) (eK.traceNext (r + 1))

/-- **The nine `𝕂′` walk-twin handle gates at the honest fill** (row `i < N`). -/
theorem walkHQ_gates_honest (eK : Env K) (eF : Env F) (N i : ℕ) (hi : i < N)
    (mL mR : ℕ → F) (xd pdL pdR : ℕ → Quad (algebraMap F K δF)) (hx0 : xd i ≠ 0) (hL0 : pdL i ≠ 0)
    (hR0 : pdR i ≠ 0)
    (hF : eF.trace WChip.isF = if i = 0 then 1 else 0)
    (hL : eF.trace WChip.isL = if i + 1 = N then 1 else 0)
    (hmL : eF.trace WChip.mL = mL i) (hmR : eF.trace WChip.mR = mR i)
    (hmLn : i + 1 < N → eF.traceNext WChip.mL = mL (i + 1))
    (hmRn : i + 1 < N → eF.traceNext WChip.mR = mR (i + 1))
    (hdx : (HQ.denKeyQ δF (WalkHC.xKeyH (F := F))).ev δF eK eF = xd i)
    (hdL : (HQ.denKeyQ δF (WalkHC.recLH (F := F))).ev δF eK eF = pdL i)
    (hdR : (HQ.denKeyQ δF (WalkHC.recRH (F := F))).ev δF eK eF = pdR i)
    (hxi : Quad.mk _ (eK.trace WalkHQ.hxInvQ) (eK.trace (WalkHQ.hxInvQ + 1)) = (xd i)⁻¹)
    (hxin : i + 1 < N → Quad.mk _ (eK.traceNext WalkHQ.hxInvQ) (eK.traceNext (WalkHQ.hxInvQ + 1)) = (xd (i + 1))⁻¹)
    (hpL : Quad.mk _ (eK.trace WalkHQ.hpInvLQ) (eK.trace (WalkHQ.hpInvLQ + 1)) = (pdL i)⁻¹) (hpR : Quad.mk _ (eK.trace WalkHQ.hpInvRQ) (eK.trace (WalkHQ.hpInvRQ + 1)) = (pdR i)⁻¹)
    (hpLn : i + 1 < N → Quad.mk _ (eK.traceNext WalkHQ.hpInvLQ) (eK.traceNext (WalkHQ.hpInvLQ + 1)) = (pdL (i + 1))⁻¹)
    (hpRn : i + 1 < N → Quad.mk _ (eK.traceNext WalkHQ.hpInvRQ) (eK.traceNext (WalkHQ.hpInvRQ + 1)) = (pdR (i + 1))⁻¹)
    (hxa : Quad.mk _ (eK.trace WalkHQ.hxAccQ) (eK.trace (WalkHQ.hxAccQ + 1)) = ∑ j ∈ Finset.range (i + 1), (xd j)⁻¹)
    (hxan : i + 1 < N → Quad.mk _ (eK.traceNext WalkHQ.hxAccQ) (eK.traceNext (WalkHQ.hxAccQ + 1)) = ∑ j ∈ Finset.range (i + 2), (xd j)⁻¹)
    (hpa : Quad.mk _ (eK.trace WalkHQ.hpAccQ) (eK.trace (WalkHQ.hpAccQ + 1)) = ∑ j ∈ Finset.range (i + 1),
      (liftQ δF (mL j) * (pdL j)⁻¹ + liftQ δF (mR j) * (pdR j)⁻¹))
    (hpan : i + 1 < N → Quad.mk _ (eK.traceNext WalkHQ.hpAccQ) (eK.traceNext (WalkHQ.hpAccQ + 1)) = ∑ j ∈ Finset.range (i + 2),
      (liftQ δF (mL j) * (pdL j)⁻¹ + liftQ δF (mR j) * (pdR j)⁻¹))
    (hpx : Quad.mk _ (eK.pub WalkHQ.pubXQ) (eK.pub (WalkHQ.pubXQ + 1)) = ∑ j ∈ Finset.range N, (xd j)⁻¹)
    (hpp : Quad.mk _ (eK.pub WalkHQ.pubPQ) (eK.pub (WalkHQ.pubPQ + 1)) = ∑ j ∈ Finset.range N,
      (liftQ δF (mL j) * (pdL j)⁻¹ + liftQ δF (mR j) * (pdR j)⁻¹)) :
    ∀ g ∈ WalkHQ.gates δF, g.eval eK eF = 0 := by
  refine flat_gates_of_ev δF _ eK eF fun e he => ?_
  simp only [WalkHQ.gatesQ, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [ev_sub, ev_mul, ev_var, hxi, hdx, ev_one, inv_mul_cancel₀ hx0, sub_self]
  · rw [ev_sub, ev_mul, ev_var, hpL, hdL, ev_one, inv_mul_cancel₀ hL0, sub_self]
  · rw [ev_sub, ev_mul, ev_var, hpR, hdR, ev_one, inv_mul_cancel₀ hR0, sub_self]
  · rw [ev_scale, ev_sub, ev_var, ev_var, hxa, hxi]
    simp only [cv, CoeffExpr.eval, hF]
    by_cases h0 : i = 0
    · subst h0; simp [liftQ]
    · simp [h0, liftQ]
  · rw [ev_scale, ev_sub, ev_sub, ev_next, ev_var, ev_next]
    simp only [notE, CoeffExpr.eval, hL]
    by_cases hl : i + 1 = N
    · simp [hl, liftQ]
    · have hlt : i + 1 < N := by omega
      rw [hxan hlt, hxa, hxin hlt, Finset.sum_range_succ _ (i + 1)]
      simp [hl, liftQ]
  · rw [ev_scale, ev_sub, ev_var, ev_pub, hxa, hpx]
    simp only [CoeffExpr.eval, hL]
    by_cases hl : i + 1 = N
    · subst hl; simp [liftQ]
    · simp [hl, liftQ]
  · rw [ev_scale, ev_sub, ev_var]
    simp only [WalkHQ.pTermQ, if_true, ev_add, ev_scale, ev_var]
    rw [hpa, hpL, hpR]
    simp only [CoeffExpr.eval, hF, hmL, hmR]
    by_cases h0 : i = 0
    · subst h0; simp [liftQ]
    · simp [h0, liftQ]
  · rw [ev_scale, ev_sub, ev_sub, ev_next, ev_var]
    simp only [WalkHQ.pTermQ, Bool.false_eq_true, if_false, ev_add, ev_scale, ev_next]
    simp only [notE, CoeffExpr.eval, hL]
    by_cases hl : i + 1 = N
    · simp [hl, liftQ]
    · have hlt : i + 1 < N := by omega
      rw [hpan hlt, hpa, hpLn hlt, hpRn hlt]
      simp only [nv, CoeffExpr.eval, hmLn hlt, hmRn hlt]
      rw [Finset.sum_range_succ _ (i + 1)]
      simp [hl, liftQ]
  · rw [ev_scale, ev_sub, ev_var, ev_pub, hpa, hpp]
    simp only [CoeffExpr.eval, hL]
    by_cases hl : i + 1 = N
    · subst hl; simp [liftQ]
    · simp [hl, liftQ]

end

end QGates

namespace WalkTraceHQ

section Data
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [Fintype K]
  (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))] (kroots : ℕ) (b : Basis (Fin 3) F K) {n : ℕ}

theorem walkTemplateHQ_width : (walkTemplateHQ δF kroots).width 3 = 166 := by
  unfold ChipTemplate.width; rw [walkTemplateHQ_baseCols, walkTemplateHQ_extCols]


theorem coordN_mod (v : K) (j : ℕ) (k : Fin 3) (h : j % 3 = k) : coordN b v j = coord b v k := by
  unfold coordN; congr 1; exact Fin.ext h

/-- The `𝕂` value at role offset `t` (`0..9`: Re / Im of `xi pl pr xa pa`). -/
def roleVal (R : WalkTraceH.Roles n (Quad (algebraMap F K δF))) (t : ℕ) (i : Fin n) : K :=
  if t = 0 then Quad.re _ (R.xi i) else if t = 1 then Quad.im _ (R.xi i)
  else if t = 2 then Quad.re _ (R.pl i) else if t = 3 then Quad.im _ (R.pl i)
  else if t = 4 then Quad.re _ (R.pr i) else if t = 5 then Quad.im _ (R.pr i)
  else if t = 6 then Quad.re _ (R.xa i) else if t = 7 then Quad.im _ (R.xa i)
  else if t = 8 then Quad.re _ (R.pa i) else Quad.im _ (R.pa i)

/-- The new `𝕂′` walk-twin columns: `kL vL kR vR` at `21..24`; role limbs at `136..165`. -/
def new (kLv vLv kRv vRv : Fin n → F) (R : WalkTraceH.Roles n (Quad (algebraMap F K δF))) : ℕ → Fin n → F := fun j i =>
  if j = 21 then kLv i else if j = 22 then vLv i else if j = 23 then kRv i else if j = 24 then vRv i
  else if 136 ≤ j ∧ j < 166 then coordN b (roleVal δF R ((j - 136) / 3) i) (j - 136) else 0

def colHQ (col : ℕ → Fin n → F) (kLv vLv kRv vRv : Fin n → F) (R : WalkTraceH.Roles n (Quad (algebraMap F K δF))) : ℕ → Fin n → F :=
  extColF 21 25 ((walkTemplate δF kroots).width 3) col (new δF b kLv vLv kRv vRv R)

end Data

section Rows
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [Fintype K]
  (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))] (kroots : ℕ) (b : Basis (Fin 3) F K) {h n : ℕ}
  (hn : 0 < n) (nodes : Fin n → F) (orbit : StrictOrbitDomain F 3 h) (chals pubs : ℕ → K)

def E (col : ℕ → Fin n → F) (kLv vLv kRv vRv : Fin n → F) (R : WalkTraceH.Roles n (Quad (algebraMap F K δF))) (i : Fin n) : Env F :=
  Reify.envOfTrace (honestQ hn nodes (colHQ δF kroots b col kLv vLv kRv vRv R)
    ((walkTemplateHQ δF kroots).width 3)) orbit.ω (nodes i) (slotVal b 25 chals) (slotVal b 25 pubs)

def denAt (l : List (CoeffExpr F)) (e : Env F) : Quad (algebraMap F K δF) :=
  (HQ.denKeyQ δF l).ev δF (gatherEnv b ((walkTemplateHQ δF kroots).col0 3) e) e

def zeroR : WalkTraceH.Roles n (Quad (algebraMap F K δF)) := ⟨fun _ => 0, fun _ => 0, fun _ => 0, fun _ => 0, fun _ => 0⟩

def dRow (l : List (CoeffExpr F)) (col : ℕ → Fin n → F) (kLv vLv kRv vRv : Fin n → F) (i : Fin n) :
    Quad (algebraMap F K δF) :=
  denAt δF kroots b l (E δF kroots b hn nodes orbit chals pubs col kLv vLv kRv vRv (zeroR (K := K) δF) i)

end Rows

section Main
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [Fintype K]
  (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))] (kroots : ℕ) (b : Basis (Fin 3) F K) {h n : ℕ}
  (hn : 0 < n) (nodes : Fin n → F) (orbit : StrictOrbitDomain F 3 h) (chals pubs : ℕ → K)
  (col : ℕ → Fin n → F) (kLv vLv kRv vRv : Fin n → F)

theorem colHQ_lt25 (R R' : WalkTraceH.Roles n (Quad (algebraMap F K δF))) (j : ℕ) (hj : j < 25) :
    colHQ δF kroots b col kLv vLv kRv vRv R j = colHQ δF kroots b col kLv vLv kRv vRv R' j := by
  funext i
  by_cases h1 : j < 21
  · simp [colHQ, extColF, h1]
  · have h2 : 21 ≤ j := by omega
    interval_cases j <;> simp [colHQ, extColF, new]

theorem E_below (R R' : WalkTraceH.Roles n (Quad (algebraMap F K δF))) (i : Fin n) (j : ℕ) (hj : j < 25) :
    (E δF kroots b hn nodes orbit chals pubs col kLv vLv kRv vRv R i).trace j =
        (E δF kroots b hn nodes orbit chals pubs col kLv vLv kRv vRv R' i).trace j ∧
    (E δF kroots b hn nodes orbit chals pubs col kLv vLv kRv vRv R i).traceNext j =
        (E δF kroots b hn nodes orbit chals pubs col kLv vLv kRv vRv R' i).traceNext j := by
  have hw : j < (walkTemplateHQ δF kroots).width 3 := by rw [walkTemplateHQ_width]; omega
  have hq := honestQ_congr hn nodes (colHQ δF kroots b col kLv vLv kRv vRv R)
    (colHQ δF kroots b col kLv vLv kRv vRv R') ((walkTemplateHQ δF kroots).width 3) ⟨j, hw⟩
    (colHQ_lt25 δF kroots b col kLv vLv kRv vRv R R' j hj)
  simp [E, Reify.envOfTrace, dif_pos hw, hq]

theorem gather_chal (e : Env F) (hc : e.chal = slotVal b 25 chals) (r : ℕ) :
    (gatherEnv b ((walkTemplateHQ δF kroots).col0 3) e).chal r = chals r := by
  simp only [gatherEnv, ChipTemplate.col0, hc, walkTemplateHQ_baseCols]
  exact sum_slotVal b 25 r chals

theorem rlcQ_congr25 (eK eK' : Env K) (eF eF' : Env F) (hc : eK.chal = eK'.chal)
    (ht : ∀ j < 25, eF.trace j = eF'.trace j) (hn : ∀ j < 25, eF.traceNext j = eF'.traceNext j) :
    ∀ (l : List (CoeffExpr F)), (∀ g ∈ l, colsBelow 25 g = true) → ∀ m,
      (HQ.rlcQ δF m l).ev δF eK eF = (HQ.rlcQ δF m l).ev δF eK' eF'
  | [], _, m => by simp [HQ.rlcQ, ev_zero]
  | g :: r, hl, m => by
      simp only [HQ.rlcQ, ev_add, ev_mul, ev_base, CellTraceHQ.gpowQ_congr δF eK eK' eF eF' hc m,
        colsBelow_eval (hl g (by simp)) ht hn,
        rlcQ_congr25 eK eK' eF eF' hc ht hn r (fun g' hg' => hl g' (by simp [hg'])) (m + 1)]

theorem denAt_congr (l : List (CoeffExpr F)) (hl : ∀ g ∈ l, colsBelow 25 g = true) (e e' : Env F)
    (hc : e.chal = slotVal b 25 chals) (hc' : e'.chal = slotVal b 25 chals)
    (ht : ∀ j < 25, e.trace j = e'.trace j) (hn : ∀ j < 25, e.traceNext j = e'.traceNext j) :
    denAt δF kroots b l e = denAt δF kroots b l e' := by
  have hcc : (gatherEnv b ((walkTemplateHQ δF kroots).col0 3) e).chal =
      (gatherEnv b ((walkTemplateHQ δF kroots).col0 3) e').chal := by
    funext r; rw [gather_chal δF kroots b chals e hc, gather_chal δF kroots b chals e' hc']
  simp only [denAt, HQ.denKeyQ, ev_add, HQ.rhoQ, ev_chal, hcc, rlcQ_congr25 δF _ _ e e' hcc ht hn _ hl 0]

theorem den_indep (l : List (CoeffExpr F)) (hl : ∀ g ∈ l, colsBelow 25 g = true) (R : WalkTraceH.Roles n (Quad (algebraMap F K δF)))
    (i : Fin n) :
    denAt δF kroots b l (E δF kroots b hn nodes orbit chals pubs col kLv vLv kRv vRv R i) =
      dRow δF kroots b hn nodes orbit chals pubs l col kLv vLv kRv vRv i :=
  denAt_congr δF kroots b chals l hl _ _ rfl rfl
    (fun j hj => (E_below δF kroots b hn nodes orbit chals pubs col kLv vLv kRv vRv R (zeroR (K := K) δF) i j hj).1)
    (fun j hj => (E_below δF kroots b hn nodes orbit chals pubs col kLv vLv kRv vRv R (zeroR (K := K) δF) i j hj).2)

def dN (l : List (CoeffExpr F)) (j : ℕ) : Quad (algebraMap F K δF) :=
  if hj : j < n then dRow δF kroots b hn nodes orbit chals pubs l col kLv vLv kRv vRv ⟨j, hj⟩ else 1

/-- **The honest `𝕂′` role fill**: inverses `den′⁻¹`, inclusive prefix sums. -/
def rolesF : WalkTraceH.Roles n (Quad (algebraMap F K δF)) where
  xi := fun i => (dRow δF kroots b hn nodes orbit chals pubs WalkHC.xKeyH col kLv vLv kRv vRv i)⁻¹
  pl := fun i => (dRow δF kroots b hn nodes orbit chals pubs WalkHC.recLH col kLv vLv kRv vRv i)⁻¹
  pr := fun i => (dRow δF kroots b hn nodes orbit chals pubs WalkHC.recRH col kLv vLv kRv vRv i)⁻¹
  xa := fun i => ∑ j ∈ Finset.range (i + 1),
    (dN δF kroots b hn nodes orbit chals pubs col kLv vLv kRv vRv WalkHC.xKeyH j)⁻¹
  pa := fun i => ∑ j ∈ Finset.range (i + 1),
    (liftQ δF (WalkTraceH.cN j (col WChip.mL)) *
        (dN δF kroots b hn nodes orbit chals pubs col kLv vLv kRv vRv WalkHC.recLH j)⁻¹ +
      liftQ δF (WalkTraceH.cN j (col WChip.mR)) *
        (dN δF kroots b hn nodes orbit chals pubs col kLv vLv kRv vRv WalkHC.recRH j)⁻¹)

/-- **`walkTraceHQ`**: the honest 166-column `𝕂′` walk twin trace. -/
def walkTraceHQ :=
  honestQ hn nodes (colHQ δF kroots b col kLv vLv kRv vRv
    (rolesF δF kroots b hn nodes orbit chals pubs col kLv vLv kRv vRv)) ((walkTemplateHQ δF kroots).width 3)

/-- **The `𝕂′` walk twin accepts `walkTraceHQ`**, from the original honest walk acceptance, boolean kind
bits, no vanishing `𝕂′` denominator and the `𝕂′` publics equal to the totals. -/
theorem walkChipHQ_accepts_honest (hinj : Function.Injective nodes)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω)
    (hsat0 : (walkChip δF kroots b hn nodes orbit chals pubs).rap.Satisfies (honestQ hn nodes col _))
    (hkL : ∀ i, kLv i = 0 ∨ kLv i = 1) (hkR : ∀ i, kRv i = 0 ∨ kRv i = 1)
    (hpX : ∀ i, dRow δF kroots b hn nodes orbit chals pubs WalkHC.xKeyH col kLv vLv kRv vRv i ≠ 0)
    (hpL : ∀ i, dRow δF kroots b hn nodes orbit chals pubs WalkHC.recLH col kLv vLv kRv vRv i ≠ 0)
    (hpR : ∀ i, dRow δF kroots b hn nodes orbit chals pubs WalkHC.recRH col kLv vLv kRv vRv i ≠ 0)
    (hpubX : Quad.mk _ (pubs WalkHQ.pubXQ) (pubs (WalkHQ.pubXQ + 1)) = ∑ j ∈ Finset.range n,
      (dN δF kroots b hn nodes orbit chals pubs col kLv vLv kRv vRv WalkHC.xKeyH j)⁻¹)
    (hpubP : Quad.mk _ (pubs WalkHQ.pubPQ) (pubs (WalkHQ.pubPQ + 1)) = ∑ j ∈ Finset.range n,
      (liftQ δF (WalkTraceH.cN j (col WChip.mL)) *
          (dN δF kroots b hn nodes orbit chals pubs col kLv vLv kRv vRv WalkHC.recLH j)⁻¹ +
        liftQ δF (WalkTraceH.cN j (col WChip.mR)) *
          (dN δF kroots b hn nodes orbit chals pubs col kLv vLv kRv vRv WalkHC.recRH j)⁻¹)) :
    (walkChipHQ δF kroots b hn nodes orbit chals pubs).rap.Satisfies
      (walkTraceHQ δF kroots b hn nodes orbit chals pubs col kLv vLv kRv vRv) := by
  have hW : (walkTemplate δF kroots).width 3 = 132 := WalkTraceH.walkTemplate_width δF kroots
  have hW' : (walkTemplateHQ δF kroots).width 3 = 166 := walkTemplateHQ_width δF kroots
  set R := rolesF δF kroots b hn nodes orbit chals pubs col kLv vLv kRv vRv with hR
  refine expandChip_extend_honest b orbit (rowNodeSet nodes) chals pubs (walkTemplate δF kroots)
    (walkTemplateHQ δF kroots) 21 25 (walkTemplate_baseCols δF kroots) (walkTemplateHQ_baseCols δF kroots)
    (by omega) (by omega) (by rw [walkTemplate_extCols, walkTemplateHQ_extCols]; omega)
    (fun g hg => ⟨List.mem_append_left _ hg, walkBase_below kroots g hg⟩)
    (fun g hg => ⟨List.mem_append_left _ hg, by rw [walkTemplate_extCols]; exact walkMixed_below δF kroots g hg⟩)
    rfl rfl hn nodes col (new δF b kLv vLv kRv vRv R) hsat0 ?_ ?_
  all_goals
    intro x hx g hg hg0
    obtain ⟨i, rfl⟩ := (mem_rowNodeSet_iff nodes x).mp hx
    have hE : Reify.envOfTrace (honestQ hn nodes (extColF 21 25 ((walkTemplate δF kroots).width 3) col
        (new δF b kLv vLv kRv vRv R)) ((walkTemplateHQ δF kroots).width 3)) orbit.ω (nodes i)
        (slotVal b 25 chals) (slotVal b 25 pubs) =
        E δF kroots b hn nodes orbit chals pubs col kLv vLv kRv vRv R i := rfl
    rw [hE]
    set e1 := E δF kroots b hn nodes orbit chals pubs col kLv vLv kRv vRv R i with he1
    have hwlt : ∀ j, j < 166 → j < (walkTemplateHQ δF kroots).width 3 := fun j hj => by omega
    have hET : ∀ j, j < 166 → e1.trace j = fullCol hn (colHQ δF kroots b col kLv vLv kRv vRv R) j i :=
      fun j hj => env_trace hn nodes hinj _ _ _ _ i (hwlt j hj)
    have hENx : ∀ (hi : (i : ℕ) + 1 < n) j, j < 166 →
        e1.traceNext j = fullCol hn (colHQ δF kroots b col kLv vLv kRv vRv R) j ⟨(i : ℕ) + 1, hi⟩ :=
      fun hi j hj => env_traceNext hn nodes hinj _ _ _ _ hadj i hi (hwlt j hj)
    have hnew : ∀ j, 2 ≤ j → fullCol hn (colHQ δF kroots b col kLv vLv kRv vRv R) j =
        colHQ δF kroots b col kLv vLv kRv vRv R j := by
      intro j hj; funext i'; simp only [fullCol]; split_ifs <;> first | omega | rfl
    have hkLc : ∀ i' : Fin n, fullCol hn (colHQ δF kroots b col kLv vLv kRv vRv R) 21 i' = kLv i' := by
      intro i'; rw [hnew _ (by omega)]; simp [colHQ, extColF, new]
    have hkRc : ∀ i' : Fin n, fullCol hn (colHQ δF kroots b col kLv vLv kRv vRv R) 23 i' = kRv i' := by
      intro i'; rw [hnew _ (by omega)]; simp [colHQ, extColF, new]
    have hbelow : ∀ j, 2 ≤ j → j < 21 → fullCol hn (colHQ δF kroots b col kLv vLv kRv vRv R) j i = col j i := by
      intro j h2 h21; rw [hnew _ h2]; simp [colHQ, extColF, h21]
    have hbelow' : ∀ (hi : (i : ℕ) + 1 < n) (j : ℕ), 2 ≤ j → j < 21 →
        fullCol hn (colHQ δF kroots b col kLv vLv kRv vRv R) j ⟨(i : ℕ) + 1, hi⟩ = col j ⟨(i : ℕ) + 1, hi⟩ := by
      intro hi j h2 h21; rw [hnew _ h2]; simp [colHQ, extColF, h21]
    have hcol0 : ∀ r k : ℕ, (walkTemplateHQ δF kroots).col0 3 .traceCur r + k = 25 + 3 * r + k := by
      intro r k; simp only [ChipTemplate.col0, walkTemplateHQ_baseCols]
    have hcolN : ∀ r k : ℕ, (walkTemplateHQ δF kroots).col0 3 .traceNext r + k = 25 + 3 * r + k := hcol0
    have hlimb : ∀ (i' : Fin n) (t : ℕ) (k : Fin 3), t < 10 →
        fullCol hn (colHQ δF kroots b col kLv vLv kRv vRv R) (136 + 3 * t + k) i' = coord b (roleVal δF R t i') k := by
      intro i' t k ht; have hk := k.isLt
      rw [hnew _ (by omega)]
      simp only [colHQ, extColF, new, hW]
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
        if_neg (by omega), if_neg (by omega), if_pos ⟨by omega, by omega⟩,
        show (136 + 3 * t + (k : ℕ) - 136) / 3 = t by omega]
      exact coordN_mod b _ _ k (by omega)
    set eK := gatherEnv b ((walkTemplateHQ δF kroots).col0 3) e1 with heK
    have hrole : ∀ t, t < 10 → eK.trace (37 + t) = roleVal δF R t i := by
      intro t ht
      refine gather_trace b _ e1 (37 + t) _ fun k => ?_
      rw [hcol0, show 25 + 3 * (37 + t) + (k : ℕ) = 136 + 3 * t + k by omega, hET _ (by omega), hlimb i t k ht]
    have hroleN : ∀ (hi : (i : ℕ) + 1 < n) t, t < 10 → eK.traceNext (37 + t) = roleVal δF R t ⟨(i : ℕ) + 1, hi⟩ := by
      intro hi t ht
      refine gather_traceNext b _ e1 (37 + t) _ fun k => ?_
      rw [hcolN, show 25 + 3 * (37 + t) + (k : ℕ) = 136 + 3 * t + k by omega, hENx hi _ (by omega),
        hlimb _ t k ht]
    have hq : ∀ (t : ℕ) (v : Quad (algebraMap F K δF)), t < 9 → Quad.re _ v = roleVal δF R t i →
        Quad.im _ v = roleVal δF R (t + 1) i → Quad.mk _ (eK.trace (37 + t)) (eK.trace (37 + t + 1)) = v := by
      intro t v ht h1 h2
      rw [hrole t (by omega), show 37 + t + 1 = 37 + (t + 1) by omega, hrole (t + 1) (by omega), ← h1, ← h2,
        Quad.mk_re_im]
    have hqN : ∀ (hi : (i : ℕ) + 1 < n) (t : ℕ) (v : Quad (algebraMap F K δF)), t < 9 →
        Quad.re _ v = roleVal δF R t ⟨(i : ℕ) + 1, hi⟩ → Quad.im _ v = roleVal δF R (t + 1) ⟨(i : ℕ) + 1, hi⟩ →
        Quad.mk _ (eK.traceNext (37 + t)) (eK.traceNext (37 + t + 1)) = v := by
      intro hi t v ht h1 h2
      rw [hroleN hi t (by omega), show 37 + t + 1 = 37 + (t + 1) by omega, hroleN hi (t + 1) (by omega), ← h1,
        ← h2, Quad.mk_re_im]
    first
    | (-- base gates
       have hg' : g ∈ WChip.baseGates (F := F) kroots ++ WalkHC.baseH := hg
       have hgb : g ∈ WalkHC.baseH (F := F) := by
         rcases List.mem_append.mp hg' with h1 | h1
         · exact absurd h1 hg0
         · exact h1
       simp only [WalkHC.baseH, List.mem_cons, List.not_mem_nil, or_false] at hgb
       rcases hgb with rfl | rfl
       · have h21 : e1.trace WalkHC.kL = kLv i := by
           show e1.trace 21 = _; rw [hET 21 (by omega), hkLc]
         rcases hkL i with h0 | h0 <;> simp [boolE, CoeffExpr.eval, cv, h21, h0]
       · have h23 : e1.trace WalkHC.kR = kRv i := by
           show e1.trace 23 = _; rw [hET 23 (by omega), hkRc]
         rcases hkR i with h0 | h0 <;> simp [boolE, CoeffExpr.eval, cv, h23, h0])
    | (-- mixed gates
       have hgm : g ∈ WalkHQ.gates δF := by
         have hg' : g ∈ WChip.mixedGates δF kroots ++ WalkHQ.gates δF := hg
         rcases List.mem_append.mp hg' with h1 | h1
         · exact absurd h1 hg0
         · exact h1
       have hd : ∀ (l : List (CoeffExpr F)) (i' : Fin n),
           dN δF kroots b hn nodes orbit chals pubs col kLv vLv kRv vRv l i' =
             dRow δF kroots b hn nodes orbit chals pubs l col kLv vLv kRv vRv i' := fun l i' => by simp [dN]
       have hmLc : e1.trace WChip.mL = WalkTraceH.cN i (col WChip.mL) := by
         show e1.trace 10 = _; rw [hET 10 (by omega), hbelow 10 (by omega) (by omega)]; simp [WalkTraceH.cN, WChip.mL]
       have hmRc : e1.trace WChip.mR = WalkTraceH.cN i (col WChip.mR) := by
         show e1.trace 11 = _; rw [hET 11 (by omega), hbelow 11 (by omega) (by omega)]; simp [WalkTraceH.cN, WChip.mR]
       have hmLn : ∀ hi : (i : ℕ) + 1 < n, e1.traceNext WChip.mL = WalkTraceH.cN ((i : ℕ) + 1) (col WChip.mL) := by
         intro hi; show e1.traceNext 10 = _
         rw [hENx hi 10 (by omega), hbelow' hi 10 (by omega) (by omega)]; simp [WalkTraceH.cN, hi, WChip.mL]
       have hmRn : ∀ hi : (i : ℕ) + 1 < n, e1.traceNext WChip.mR = WalkTraceH.cN ((i : ℕ) + 1) (col WChip.mR) := by
         intro hi; show e1.traceNext 11 = _
         rw [hENx hi 11 (by omega), hbelow' hi 11 (by omega) (by omega)]; simp [WalkTraceH.cN, hi, WChip.mR]
       refine QGates.walkHQ_gates_honest δF eK e1 n i i.isLt
         (fun j => WalkTraceH.cN j (col WChip.mL)) (fun j => WalkTraceH.cN j (col WChip.mR))
         (dN δF kroots b hn nodes orbit chals pubs col kLv vLv kRv vRv WalkHC.xKeyH)
         (dN δF kroots b hn nodes orbit chals pubs col kLv vLv kRv vRv WalkHC.recLH)
         (dN δF kroots b hn nodes orbit chals pubs col kLv vLv kRv vRv WalkHC.recRH)
         ?_ ?_ ?_ ?_ ?_ hmLc hmRc hmLn hmRn ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ g hgm
       · rw [hd]; exact hpX i
       · rw [hd]; exact hpL i
       · rw [hd]; exact hpR i
       · show e1.trace 0 = _
         rw [hET 0 (by omega)]; simp [fullCol]
       · show e1.trace 1 = _
         rw [hET 1 (by omega)]
         simp only [fullCol, one_ne_zero, if_false, if_true]
         by_cases hl : (i : ℕ) + 1 = n
         · rw [if_pos hl, if_pos]; exact Fin.ext (by simp; omega)
         · rw [if_neg hl, if_neg]; intro hh; apply hl; have := congrArg Fin.val hh; simp at this; omega
       · exact (den_indep δF kroots b hn nodes orbit chals pubs col kLv vLv kRv vRv _
           (WalkTraceH.keys_below _ (Or.inl rfl)) R i).trans (hd _ i).symm
       · exact (den_indep δF kroots b hn nodes orbit chals pubs col kLv vLv kRv vRv _
           (WalkTraceH.keys_below _ (Or.inr (Or.inl rfl))) R i).trans (hd _ i).symm
       · exact (den_indep δF kroots b hn nodes orbit chals pubs col kLv vLv kRv vRv _
           (WalkTraceH.keys_below _ (Or.inr (Or.inr rfl))) R i).trans (hd _ i).symm
       · exact (hq 0 _ (by omega) rfl rfl).trans (by simp [R, rolesF, dN])
       · intro hi; exact (hqN hi 0 _ (by omega) rfl rfl).trans (by simp [R, rolesF, dN, hi])
       · exact (hq 2 _ (by omega) rfl rfl).trans (by simp [R, rolesF, dN])
       · exact (hq 4 _ (by omega) rfl rfl).trans (by simp [R, rolesF, dN])
       · intro hi; exact (hqN hi 2 _ (by omega) rfl rfl).trans (by simp [R, rolesF, dN, hi])
       · intro hi; exact (hqN hi 4 _ (by omega) rfl rfl).trans (by simp [R, rolesF, dN, hi])
       · exact hq 6 _ (by omega) rfl rfl
       · intro hi; exact hqN hi 6 _ (by omega) rfl rfl
       · exact hq 8 _ (by omega) rfl rfl
       · intro hi; exact hqN hi 8 _ (by omega) rfl rfl
       · rw [← hpubX]
         congr 1
         · simp only [heK, gatherEnv, ChipTemplate.col0, walkTemplateHQ_baseCols]
           exact sum_slotVal b 25 WalkHQ.pubXQ pubs
         · simp only [heK, gatherEnv, ChipTemplate.col0, walkTemplateHQ_baseCols]
           exact sum_slotVal b 25 (WalkHQ.pubXQ + 1) pubs
       · rw [← hpubP]
         congr 1
         · simp only [heK, gatherEnv, ChipTemplate.col0, walkTemplateHQ_baseCols]
           exact sum_slotVal b 25 WalkHQ.pubPQ pubs
         · simp only [heK, gatherEnv, ChipTemplate.col0, walkTemplateHQ_baseCols]
           exact sum_slotVal b 25 (WalkHQ.pubPQ + 1) pubs)

end Main

end WalkTraceHQ

end

end Nock.NockVMROM.Thm54.VclL.Handle
