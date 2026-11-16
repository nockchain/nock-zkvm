import Nock.NockVMROM.Thm54.VclL.Handle.AtomChipHQ
import Nock.NockVMROM.Thm54.VclL.Handle.CellTraceHQ
import Nock.NockVMROM.Thm54.VclL.Handle.HonestK8

/-!
The honest 349-column atom twin trace `atomTraceHQ` and its acceptance by `atomChipHQ`.  It defines
the `𝕂′` LogUp triple gates (`tripList`, `trip_gates`), the honest fill of the added columns (base
`130..204` and role limbs `313..348`), the row environments `E1` / `EK` with their agreement lemmas,
the generic LogUp block at the honest fill (`atom_block`), and the theorem
`atomChipHQ_accepts_honest`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace Nock.NockVMROM.Thm54.VclL.Handle.HonestA8

open Nock Nock.Reified Nock.Framework
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.VclL.Handle Nock.NockVMROM.Thm54.VclL.Handle.RangeHQ
open Nock.NockVMROM.Thm54.VclL.Handle.AtomChipHQ Nock.NockVMROM.Thm54.VclL.Handle.QGates
open Module
open scoped Polynomial

noncomputable section

section Trip
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [Fintype K]
  (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))]

/-- The four gates of one `𝕂′` LogUp block of `atomQ`. -/
def tripList (δF : F) (inv acc m p : ℕ) (D : QE F) : List (QE F) :=
  [ QE.sub (QE.mul δF (QE.var inv) D) QE.one,
    QE.scale (cv Cell.isF) (QE.sub (QE.var acc) (QE.scale (cv m) (QE.var inv))),
    QE.scale (notE (cv Cell.isL)) (QE.sub (QE.sub (QE.next acc) (QE.var acc))
      (QE.scale (nv m) (QE.next inv))),
    QE.scale (cv Cell.isL) (QE.sub (QE.var acc) (QE.pub p)) ]

/-- **One `𝕂′` LogUp triple at the honest fill** (inverse `inv`, accumulator `acc`, multiplicity column
`m`, terminal public `p`, denominator `D`), the four gates of `atomQ`'s three blocks. -/
theorem trip_gates (inv acc m p : ℕ) (D : QE F) (eK : Env K) (eF : Env F) (N i : ℕ) (hi : i < N)
    (mm : ℕ → F) (d : ℕ → Quad (algebraMap F K δF)) (hd0 : d i ≠ 0)
    (hF : eF.trace Cell.isF = if i = 0 then 1 else 0)
    (hL : eF.trace Cell.isL = if i + 1 = N then 1 else 0)
    (hm : eF.trace m = mm i) (hmn : i + 1 < N → eF.traceNext m = mm (i + 1))
    (hden : D.ev δF eK eF = d i)
    (hinv : Quad.mk _ (eK.trace inv) (eK.trace (inv + 1)) = (d i)⁻¹)
    (hinvn : i + 1 < N → Quad.mk _ (eK.traceNext inv) (eK.traceNext (inv + 1)) = (d (i + 1))⁻¹)
    (hacc : Quad.mk _ (eK.trace acc) (eK.trace (acc + 1)) =
      ∑ j ∈ Finset.range (i + 1), liftQ δF (mm j) * (d j)⁻¹)
    (haccn : i + 1 < N → Quad.mk _ (eK.traceNext acc) (eK.traceNext (acc + 1)) =
      ∑ j ∈ Finset.range (i + 2), liftQ δF (mm j) * (d j)⁻¹)
    (hpub : Quad.mk _ (eK.pub p) (eK.pub (p + 1)) = ∑ j ∈ Finset.range N, liftQ δF (mm j) * (d j)⁻¹) :
    ∀ e ∈ tripList δF inv acc m p D, e.ev δF eK eF = 0 := by
  intro e he
  simp only [tripList, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl
  · rw [ev_sub, ev_mul, ev_var, hinv, hden, ev_one, inv_mul_cancel₀ hd0, sub_self]
  · rw [ev_scale, ev_sub, ev_var, ev_scale, ev_var, hacc, hinv]
    simp only [cv, CoeffExpr.eval, hF, hm]
    by_cases h0 : i = 0
    · subst h0; simp [liftQ]
    · simp [h0, liftQ]
  · rw [ev_scale, ev_sub, ev_sub, ev_next, ev_var, ev_scale, ev_next]
    simp only [notE, cv, nv, CoeffExpr.eval, hL]
    by_cases hl : i + 1 = N
    · simp [hl, liftQ]
    · have hlt : i + 1 < N := by omega
      rw [haccn hlt, hacc, hinvn hlt, hmn hlt, Finset.sum_range_succ _ (i + 1)]
      simp [hl, liftQ]
  · rw [ev_scale, ev_sub, ev_var, ev_pub, hacc, hpub]
    simp only [cv, CoeffExpr.eval, hL]
    by_cases hl : i + 1 = N
    · subst hl; simp [liftQ]
    · simp [hl, liftQ]

end Trip


section Main
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [Fintype K]
  (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))] (b : Basis (Fin 3) F K) {h n : ℕ} (hn : 0 < n)
  (nodes : Fin n → F) (orbit : StrictOrbitDomain F 3 h) (chals pubs : ℕ → K)
  (col newB : ℕ → Fin n → F)

theorem atomTemplateHQ_width : (atomTemplateHQ δF).width 3 = 349 := by
  unfold ChipTemplate.width; rw [atomTemplateHQ_baseCols, atomTemplateHQ_extCols]

/-- The added columns with the `𝕂′` roles zero. -/
def newZ : ℕ → Fin n → F := fun j i => if j < 313 then newB j i else 0

/-- The zero-role-fill column function and row environment. -/
def colZ : ℕ → Fin n → F := extColF 130 205 ((cellTemplateHQ δF).width 3) col (newZ newB)

def EZ (i : Fin n) : Env F :=
  Reify.envOfTrace (honestQ hn nodes (colZ δF col newB) ((atomTemplateHQ δF).width 3)) orbit.ω (nodes i)
    (slotVal b 205 chals) (slotVal b 205 pubs)

/-- The three `𝕂′` denominators at the zero-role-fill row. -/
def dMB (i : Fin n) : Quad (algebraMap F K δF) :=
  (den δF (mbKey (F := F))).ev δF (gatherEnv b ((atomTemplateHQ δF).col0 3)
    (EZ δF b hn nodes orbit chals pubs col newB i)) (EZ δF b hn nodes orbit chals pubs col newB i)
def dC (i : Fin n) : Quad (algebraMap F K δF) :=
  (HQ.denKeyQ δF (oldKey (F := F))).ev δF (gatherEnv b ((atomTemplateHQ δF).col0 3)
    (EZ δF b hn nodes orbit chals pubs col newB i)) (EZ δF b hn nodes orbit chals pubs col newB i)
def dMI (i : Fin n) : Quad (algebraMap F K δF) :=
  (HQ.denKeyQ δF (incKey (F := F))).ev δF (gatherEnv b ((atomTemplateHQ δF).col0 3)
    (EZ δF b hn nodes orbit chals pubs col newB i)) (EZ δF b hn nodes orbit chals pubs col newB i)

end Main

theorem den_below {F : Type} [Field F] (δF : F) :
    mixBelow 36 205 (den δF (mbKey (F := F))).re = true ∧ mixBelow 36 205 (den δF (mbKey (F := F))).im = true ∧
    mixBelow 36 205 (HQ.denKeyQ δF (oldKey (F := F))).re = true ∧ mixBelow 36 205 (HQ.denKeyQ δF (oldKey (F := F))).im = true ∧
    mixBelow 36 205 (HQ.denKeyQ δF (incKey (F := F))).re = true ∧ mixBelow 36 205 (HQ.denKeyQ δF (incKey (F := F))).im = true := by
  simp [den, QE.rlc, QE.add, QE.mul, QE.gpow, rQ, mbKey, zAt, QE.var, QE.chal, QE.zero, QE.base, mixBelow,
    colsBelow, List.zipIdx, cv, Cell.pR, Cell.idx, HQ.denKeyQ, HQ.rlcQ, HQ.rhoQ, HQ.gpowQ, HQ.gamQ, oldKey, incKey, idxO, lO, kRO, vRO, conv,
    notE, QE.sub, QE.scale, QE.one]


section Main2
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [Fintype K]
  (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))] (b : Basis (Fin 3) F K) {h n : ℕ} (hn : 0 < n)
  (nodes : Fin n → F) (orbit : StrictOrbitDomain F 3 h) (chals pubs : ℕ → K)
  (col newB : ℕ → Fin n → F)

def cNat (j : ℕ) (c : Fin n → F) : F := if hj : j < n then c ⟨j, hj⟩ else 0
def dNat (d : Fin n → Quad (algebraMap F K δF)) (j : ℕ) : Quad (algebraMap F K δF) :=
  if hj : j < n then d ⟨j, hj⟩ else 1

/-- Honest accumulator: inclusive prefix sum of `m · d⁻¹`. -/
def accOf (m : Fin n → F) (d : Fin n → Quad (algebraMap F K δF)) (i : Fin n) : Quad (algebraMap F K δF) :=
  ∑ j ∈ Finset.range (i + 1), liftQ δF (cNat j m) * (dNat δF d j)⁻¹

/-- The twelve `𝕂`-role values (Re/Im of `mbInv, mbAcc, cInv, miInv, miAcc, cAcc`). -/
def roleValA (t : ℕ) (i : Fin n) : K :=
  let iMB := (dMB δF b hn nodes orbit chals pubs col newB i)⁻¹
  let aMB := accOf δF (newB mb) (dMB δF b hn nodes orbit chals pubs col newB) i
  let iC := (dC δF b hn nodes orbit chals pubs col newB i)⁻¹
  let aC := accOf δF (newB inc) (dC δF b hn nodes orbit chals pubs col newB) i
  let iMI := (dMI δF b hn nodes orbit chals pubs col newB i)⁻¹
  let aMI := accOf δF (newB mi) (dMI δF b hn nodes orbit chals pubs col newB) i
  if t = 0 then Quad.re _ iMB else if t = 1 then Quad.im _ iMB
  else if t = 2 then Quad.re _ aMB else if t = 3 then Quad.im _ aMB
  else if t = 4 then Quad.re _ iC else if t = 5 then Quad.im _ iC
  else if t = 6 then Quad.re _ iMI else if t = 7 then Quad.im _ iMI
  else if t = 8 then Quad.re _ aMI else if t = 9 then Quad.im _ aMI
  else if t = 10 then Quad.re _ aC else Quad.im _ aC

/-- The added columns: base `130..204` from `newB`, role limbs at `313..348`. -/
def newFull : ℕ → Fin n → F := fun j i =>
  if j < 313 then newB j i
  else coordN b (roleValA δF b hn nodes orbit chals pubs col newB ((j - 313) / 3) i) (j - 313)

def colA : ℕ → Fin n → F := extColF 130 205 ((cellTemplateHQ δF).width 3) col
  (newFull δF b hn nodes orbit chals pubs col newB)

/-- **The honest 349-column atom twin trace.** -/
def atomTraceHQ := honestQ hn nodes (colA δF b hn nodes orbit chals pubs col newB) 349


theorem coordN_mod3 (v : K) (j : ℕ) (k : Fin 3) (hj : j % 3 = k) : coordN b v j = coord b v k := by
  unfold coordN; congr 1; exact Fin.ext hj

/-- The honest atom row environment (row `i`, full 349-column trace). -/
def E1 (i : Fin n) : Env F :=
  Reify.envOfTrace (honestQ hn nodes (colA δF b hn nodes orbit chals pubs col newB) 349) orbit.ω (nodes i)
    (slotVal b 205 chals) (slotVal b 205 pubs)

/-- The gathered `𝕂′` row environment. -/
def EK (i : Fin n) : Env K := gatherEnv b ((atomTemplateHQ δF).col0 3) (E1 δF b hn nodes orbit chals pubs col newB i)

theorem E1_agree (i : Fin n) : ∀ j, j < 313 →
    (E1 δF b hn nodes orbit chals pubs col newB i).trace j =
        (EZ δF b hn nodes orbit chals pubs col newB i).trace j ∧
      (E1 δF b hn nodes orbit chals pubs col newB i).traceNext j =
        (EZ δF b hn nodes orbit chals pubs col newB i).traceNext j := by
  have hWA : (atomTemplateHQ δF).width 3 = 349 := atomTemplateHQ_width δF
  have hP : ∀ j : Fin 349, (j : ℕ) < 313 →
      honestQ hn nodes (colA δF b hn nodes orbit chals pubs col newB) 349 j =
        honestQ hn nodes (colZ δF col newB) 349 j := by
    intro j hj
    refine honestQ_congr hn nodes _ _ 349 j ?_
    funext i'
    simp only [colA, colZ, extColF, newFull, newZ]
    split_ifs <;> first | rfl | omega
  intro j hj
  simp only [E1, EZ, Reify.envOfTrace, hWA, dif_pos (show j < 349 by omega)]
  have := hP ⟨j, by omega⟩ hj
  rw [this]
  exact ⟨rfl, rfl⟩

theorem E1_isF (hinj : Function.Injective nodes) (i : Fin n) :
    (E1 δF b hn nodes orbit chals pubs col newB i).trace Cell.isF = if (i : ℕ) = 0 then 1 else 0 := by
  show (E1 δF b hn nodes orbit chals pubs col newB i).trace 0 = _
  unfold E1
  rw [env_trace hn nodes hinj _ _ _ _ i (by omega : 0 < 349)]; simp [fullCol]

theorem E1_isL (hinj : Function.Injective nodes) (i : Fin n) :
    (E1 δF b hn nodes orbit chals pubs col newB i).trace Cell.isL = if (i : ℕ) + 1 = n then 1 else 0 := by
  show (E1 δF b hn nodes orbit chals pubs col newB i).trace 1 = _
  unfold E1
  rw [env_trace hn nodes hinj _ _ _ _ i (by omega : 1 < 349)]
  simp only [fullCol, one_ne_zero, if_false, if_true]
  by_cases hl : (i : ℕ) + 1 = n
  · rw [if_pos hl, if_pos]; exact Fin.ext (by simp; omega)
  · rw [if_neg hl, if_neg]; intro hh; apply hl; have := congrArg Fin.val hh; simp at this; omega

theorem fullCol_mcol (c : ℕ) (h1 : 130 ≤ c) (h2 : c < 205) (i' : Fin n) :
    fullCol hn (colA δF b hn nodes orbit chals pubs col newB) c i' = newB c i' := by
  have hW' : (cellTemplateHQ δF).width 3 = 238 := CellTraceHQ.cellTemplateHQ_width δF
  simp only [fullCol, colA, extColF, newFull]
  split_ifs <;> first | rfl | (exfalso; omega)

theorem E1_mult (hinj : Function.Injective nodes)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω)
    (i : Fin n) (c : ℕ) (h1 : 130 ≤ c) (h2 : c < 205) :
    (E1 δF b hn nodes orbit chals pubs col newB i).trace c = cNat i (newB c) ∧
      (∀ hi : (i : ℕ) + 1 < n, (E1 δF b hn nodes orbit chals pubs col newB i).traceNext c =
        cNat ((i : ℕ) + 1) (newB c)) := by
  refine ⟨?_, fun hi => ?_⟩
  · unfold E1
    rw [env_trace hn nodes hinj _ _ _ _ i (by omega : c < 349), fullCol_mcol δF b hn nodes orbit chals pubs col newB c h1 h2]
    simp [cNat]
  · unfold E1
    rw [env_traceNext hn nodes hinj _ _ _ _ hadj i hi (by omega : c < 349),
      fullCol_mcol δF b hn nodes orbit chals pubs col newB c h1 h2]
    simp [cNat, hi]

theorem fullCol_limb (i' : Fin n) (t : ℕ) (k : Fin 3) (ht : t < 12) :
    fullCol hn (colA δF b hn nodes orbit chals pubs col newB) (313 + 3 * t + k) i' =
      coord b (roleValA δF b hn nodes orbit chals pubs col newB t i') k := by
  have hk := k.isLt
  have h1 : ¬ (313 + 3 * t + (k : ℕ) < 313) := by omega
  have h2 : ¬ (313 + 3 * t + (k : ℕ) < 205) := by omega
  have h3 : ¬ (313 + 3 * t + (k : ℕ) < 130) := by omega
  have hW' : (cellTemplateHQ δF).width 3 = 238 := CellTraceHQ.cellTemplateHQ_width δF
  have h4 : ¬ (313 + 3 * t + (k : ℕ) < (cellTemplateHQ δF).width 3 + (205 - 130)) := by omega
  have h0 : ¬ (313 + 3 * t + (k : ℕ) = 0) := by omega
  have h0' : ¬ (313 + 3 * t + (k : ℕ) = 1) := by omega
  simp only [fullCol, colA, extColF, newFull, h0, h0', h1, h2, h3, h4, if_false]
  rw [show (313 + 3 * t + (k : ℕ) - 313) / 3 = t by omega]
  exact coordN_mod3 b _ (313 + 3 * t + (k : ℕ) - 313) k (by omega)

theorem EK_trace_role (hinj : Function.Injective nodes) (i : Fin n) (t : ℕ) (ht : t < 12) :
    (EK δF b hn nodes orbit chals pubs col newB i).trace (36 + t) =
      roleValA δF b hn nodes orbit chals pubs col newB t i := by
  refine gather_trace b _ _ (36 + t) _ fun k => ?_
  have hcol0 : (atomTemplateHQ δF).col0 3 .traceCur (36 + t) + k = 205 + 3 * (36 + t) + k := by
    simp only [ChipTemplate.col0, atomTemplateHQ_baseCols]
  rw [hcol0, show 205 + 3 * (36 + t) + (k : ℕ) = 313 + 3 * t + k by omega]
  unfold E1
  rw [env_trace hn nodes hinj _ _ _ _ i (by have := k.isLt; omega),
    fullCol_limb δF b hn nodes orbit chals pubs col newB i t k ht]

theorem EK_traceNext_role (hinj : Function.Injective nodes)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω)
    (i : Fin n) (hi : (i : ℕ) + 1 < n) (t : ℕ) (ht : t < 12) :
    (EK δF b hn nodes orbit chals pubs col newB i).traceNext (36 + t) =
      roleValA δF b hn nodes orbit chals pubs col newB t ⟨(i : ℕ) + 1, hi⟩ := by
  refine gather_traceNext b _ _ (36 + t) _ fun k => ?_
  have hcolN : (atomTemplateHQ δF).col0 3 .traceNext (36 + t) + k = 205 + 3 * (36 + t) + k := by
    simp only [ChipTemplate.col0, atomTemplateHQ_baseCols]
  rw [hcolN, show 205 + 3 * (36 + t) + (k : ℕ) = 313 + 3 * t + k by omega]
  unfold E1
  rw [env_traceNext hn nodes hinj _ _ _ _ hadj i hi (by have := k.isLt; omega),
    fullCol_limb δF b hn nodes orbit chals pubs col newB _ t k ht]

theorem EK_quad (hinj : Function.Injective nodes) (i : Fin n) (t : ℕ) (ht : t + 1 < 12)
    (v : Quad (algebraMap F K δF))
    (h1 : Quad.re _ v = roleValA δF b hn nodes orbit chals pubs col newB t i)
    (h2 : Quad.im _ v = roleValA δF b hn nodes orbit chals pubs col newB (t + 1) i) :
    Quad.mk _ ((EK δF b hn nodes orbit chals pubs col newB i).trace (36 + t))
      ((EK δF b hn nodes orbit chals pubs col newB i).trace (36 + t + 1)) = v := by
  rw [EK_trace_role δF b hn nodes orbit chals pubs col newB hinj i t (by omega),
    show 36 + t + 1 = 36 + (t + 1) by omega,
    EK_trace_role δF b hn nodes orbit chals pubs col newB hinj i (t + 1) (by omega), ← h1, ← h2, Quad.mk_re_im]

theorem EK_quadN (hinj : Function.Injective nodes)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω)
    (i : Fin n) (hi : (i : ℕ) + 1 < n) (t : ℕ) (ht : t + 1 < 12)
    (v : Quad (algebraMap F K δF))
    (h1 : Quad.re _ v = roleValA δF b hn nodes orbit chals pubs col newB t ⟨(i : ℕ) + 1, hi⟩)
    (h2 : Quad.im _ v = roleValA δF b hn nodes orbit chals pubs col newB (t + 1) ⟨(i : ℕ) + 1, hi⟩) :
    Quad.mk _ ((EK δF b hn nodes orbit chals pubs col newB i).traceNext (36 + t))
      ((EK δF b hn nodes orbit chals pubs col newB i).traceNext (36 + t + 1)) = v := by
  rw [EK_traceNext_role δF b hn nodes orbit chals pubs col newB hinj hadj i hi t (by omega),
    show 36 + t + 1 = 36 + (t + 1) by omega,
    EK_traceNext_role δF b hn nodes orbit chals pubs col newB hinj hadj i hi (t + 1) (by omega),
    ← h1, ← h2, Quad.mk_re_im]

theorem EK_den (i : Fin n) (D : QE F) (h1 : mixBelow 36 205 D.re = true) (h2 : mixBelow 36 205 D.im = true) :
    D.ev δF (EK δF b hn nodes orbit chals pubs col newB i) (E1 δF b hn nodes orbit chals pubs col newB i) =
      D.ev δF (gatherEnv b ((atomTemplateHQ δF).col0 3) (EZ δF b hn nodes orbit chals pubs col newB i))
        (EZ δF b hn nodes orbit chals pubs col newB i) := by
  have hag := E1_agree δF b hn nodes orbit chals pubs col newB i
  have hKt : ∀ r < 36, (EK δF b hn nodes orbit chals pubs col newB i).trace r =
      (gatherEnv b ((atomTemplateHQ δF).col0 3) (EZ δF b hn nodes orbit chals pubs col newB i)).trace r := by
    intro r hr
    simp only [EK, gatherEnv]
    exact Finset.sum_congr rfl fun k _ => by
      have hk := k.isLt
      rw [(hag _ (by simp only [ChipTemplate.col0, atomTemplateHQ_baseCols]; omega)).1]
  have hKn : ∀ r < 36, (EK δF b hn nodes orbit chals pubs col newB i).traceNext r =
      (gatherEnv b ((atomTemplateHQ δF).col0 3) (EZ δF b hn nodes orbit chals pubs col newB i)).traceNext r := by
    intro r hr
    simp only [EK, gatherEnv]
    exact Finset.sum_congr rfl fun k _ => by
      have hk := k.isLt
      rw [(hag _ (by simp only [ChipTemplate.col0, atomTemplateHQ_baseCols]; omega)).2]
  simp only [QE.ev]
  congr 1
  · exact mixBelow_eval h1 hKt hKn rfl rfl (fun j hj => (hag j (by omega)).1)
      (fun j hj => (hag j (by omega)).2)
  · exact mixBelow_eval h2 hKt hKn rfl rfl (fun j hj => (hag j (by omega)).1)
      (fun j hj => (hag j (by omega)).2)

theorem EK_pub (i : Fin n) (p : ℕ) :
    (EK δF b hn nodes orbit chals pubs col newB i).pub p = pubs p := by
  simp only [EK, gatherEnv, ChipTemplate.col0, atomTemplateHQ_baseCols]
  exact sum_slotVal b 205 p pubs

/-- The three role-value quads, for the pair arguments. -/
theorem roleValA_re_im (i : Fin n) :
    roleValA δF b hn nodes orbit chals pubs col newB 0 i = Quad.re _ (dMB δF b hn nodes orbit chals pubs col newB i)⁻¹ ∧
    roleValA δF b hn nodes orbit chals pubs col newB 1 i = Quad.im _ (dMB δF b hn nodes orbit chals pubs col newB i)⁻¹ ∧
    roleValA δF b hn nodes orbit chals pubs col newB 2 i = Quad.re _ (accOf δF (newB mb) (dMB δF b hn nodes orbit chals pubs col newB) i) ∧
    roleValA δF b hn nodes orbit chals pubs col newB 3 i = Quad.im _ (accOf δF (newB mb) (dMB δF b hn nodes orbit chals pubs col newB) i) ∧
    roleValA δF b hn nodes orbit chals pubs col newB 4 i = Quad.re _ (dC δF b hn nodes orbit chals pubs col newB i)⁻¹ ∧
    roleValA δF b hn nodes orbit chals pubs col newB 5 i = Quad.im _ (dC δF b hn nodes orbit chals pubs col newB i)⁻¹ ∧
    roleValA δF b hn nodes orbit chals pubs col newB 6 i = Quad.re _ (dMI δF b hn nodes orbit chals pubs col newB i)⁻¹ ∧
    roleValA δF b hn nodes orbit chals pubs col newB 7 i = Quad.im _ (dMI δF b hn nodes orbit chals pubs col newB i)⁻¹ ∧
    roleValA δF b hn nodes orbit chals pubs col newB 8 i = Quad.re _ (accOf δF (newB mi) (dMI δF b hn nodes orbit chals pubs col newB) i) ∧
    roleValA δF b hn nodes orbit chals pubs col newB 9 i = Quad.im _ (accOf δF (newB mi) (dMI δF b hn nodes orbit chals pubs col newB) i) ∧
    roleValA δF b hn nodes orbit chals pubs col newB 10 i = Quad.re _ (accOf δF (newB inc) (dC δF b hn nodes orbit chals pubs col newB) i) ∧
    roleValA δF b hn nodes orbit chals pubs col newB 11 i = Quad.im _ (accOf δF (newB inc) (dC δF b hn nodes orbit chals pubs col newB) i) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [roleValA]

/-- **Generic block**: a `𝕂′` LogUp block at the honest fill, with the role pair `t` (inverse),
`t + 2`/`t'` (accumulator) given as quad facts. -/
theorem atom_block (hinj : Function.Injective nodes)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω)
    (i : Fin n) (inv acc m p : ℕ) (D : QE F) (tI tA : ℕ) (hI : inv = 36 + tI) (hA : acc = 36 + tA)
    (htI : tI + 1 < 12) (htA : tA + 1 < 12) (hm1 : 130 ≤ m) (hm2 : m < 205)
    (hD1 : mixBelow 36 205 D.re = true) (hD2 : mixBelow 36 205 D.im = true)
    (d : Fin n → Quad (algebraMap F K δF))
    (hdd : D.ev δF (gatherEnv b ((atomTemplateHQ δF).col0 3) (EZ δF b hn nodes orbit chals pubs col newB i))
        (EZ δF b hn nodes orbit chals pubs col newB i) = d i)
    (hz : ∀ i, d i ≠ 0)
    (hI0 : ∀ i', Quad.re _ (d i')⁻¹ = roleValA δF b hn nodes orbit chals pubs col newB tI i' ∧
      Quad.im _ (d i')⁻¹ = roleValA δF b hn nodes orbit chals pubs col newB (tI + 1) i')
    (hA0 : ∀ i', Quad.re _ (accOf δF (newB m) d i') = roleValA δF b hn nodes orbit chals pubs col newB tA i' ∧
      Quad.im _ (accOf δF (newB m) d i') = roleValA δF b hn nodes orbit chals pubs col newB (tA + 1) i')
    (hp : Quad.mk _ (pubs p) (pubs (p + 1)) = ∑ j ∈ Finset.range n, liftQ δF (cNat j (newB m)) * (dNat δF d j)⁻¹)
    (hpe : (EK δF b hn nodes orbit chals pubs col newB i).pub p = pubs p ∧
      (EK δF b hn nodes orbit chals pubs col newB i).pub (p + 1) = pubs (p + 1)) :
    ∀ e ∈ tripList δF inv acc m p D,
      e.ev δF (EK δF b hn nodes orbit chals pubs col newB i) (E1 δF b hn nodes orbit chals pubs col newB i) = 0 := by
  subst hI hA
  have hmu := E1_mult δF b hn nodes orbit chals pubs col newB hinj hadj i m hm1 hm2
  refine trip_gates δF (36 + tI) (36 + tA) m p D _ _ n i i.isLt (fun j => cNat j (newB m)) (dNat δF d)
    (by simp [dNat, hz i]) (E1_isF δF b hn nodes orbit chals pubs col newB hinj i)
    (E1_isL δF b hn nodes orbit chals pubs col newB hinj i) hmu.1 hmu.2
    (by rw [EK_den δF b hn nodes orbit chals pubs col newB i D hD1 hD2, hdd]; simp [dNat])
    (by
      refine EK_quad δF b hn nodes orbit chals pubs col newB hinj i tI htI _ ?_ ?_
      · simpa [dNat] using (hI0 i).1
      · simpa [dNat] using (hI0 i).2)
    (fun hi => by
      refine EK_quadN δF b hn nodes orbit chals pubs col newB hinj hadj i hi tI htI _ ?_ ?_
      · simpa [dNat, hi] using (hI0 ⟨(i : ℕ) + 1, hi⟩).1
      · simpa [dNat, hi] using (hI0 ⟨(i : ℕ) + 1, hi⟩).2)
    (by
      refine EK_quad δF b hn nodes orbit chals pubs col newB hinj i tA htA _ ?_ ?_
      · simpa [accOf] using (hA0 i).1
      · simpa [accOf] using (hA0 i).2)
    (fun hi => by
      refine EK_quadN δF b hn nodes orbit chals pubs col newB hinj hadj i hi tA htA _ ?_ ?_
      · have := (hA0 ⟨(i : ℕ) + 1, hi⟩).1
        simpa [accOf] using this
      · have := (hA0 ⟨(i : ℕ) + 1, hi⟩).2
        simpa [accOf] using this)
    (by rw [← hp, hpe.1, hpe.2])

theorem atomChipHQ_accepts_honest (hinj : Function.Injective nodes)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω)
    (hsat0 : (cellChipHQ δF b hn nodes orbit chals pubs).rap.Satisfies (honestQ hn nodes col _))
    (hbase : ∀ i, ∀ g ∈ (atomGates (F := F)),
      g.eval (EZ δF b hn nodes orbit chals pubs col newB i) = 0)
    (hz1 : ∀ i, dMB δF b hn nodes orbit chals pubs col newB i ≠ 0)
    (hz2 : ∀ i, dC δF b hn nodes orbit chals pubs col newB i ≠ 0)
    (hz3 : ∀ i, dMI δF b hn nodes orbit chals pubs col newB i ≠ 0)
    (hpMB : Quad.mk _ (pubs pubMB) (pubs (pubMB + 1)) = ∑ j ∈ Finset.range n,
      liftQ δF (cNat j (newB mb)) * (dNat δF (dMB δF b hn nodes orbit chals pubs col newB) j)⁻¹)
    (hpC : Quad.mk _ (pubs pubC) (pubs (pubC + 1)) = ∑ j ∈ Finset.range n,
      liftQ δF (cNat j (newB inc)) * (dNat δF (dC δF b hn nodes orbit chals pubs col newB) j)⁻¹)
    (hpMI : Quad.mk _ (pubs pubMI) (pubs (pubMI + 1)) = ∑ j ∈ Finset.range n,
      liftQ δF (cNat j (newB mi)) * (dNat δF (dMI δF b hn nodes orbit chals pubs col newB) j)⁻¹) :
    (atomChipHQ δF b hn nodes orbit chals pubs).rap.Satisfies
      (atomTraceHQ δF b hn nodes orbit chals pubs col newB) := by
  have hW' : (cellTemplateHQ δF).width 3 = 238 := CellTraceHQ.cellTemplateHQ_width δF
  have hWA : (atomTemplateHQ δF).width 3 = 349 := atomTemplateHQ_width δF
  obtain ⟨hB, hM, -, -⟩ := cellHQ_range δF
  have hP : ∀ j : Fin 349, (j : ℕ) < 313 →
      honestQ hn nodes (colA δF b hn nodes orbit chals pubs col newB) 349 j =
        honestQ hn nodes (colZ δF col newB) 349 j := by
    intro j hj
    refine honestQ_congr hn nodes _ _ 349 j ?_
    funext i'
    simp only [colA, colZ, extColF, newFull, newZ]
    split_ifs <;> first | rfl | omega
  have key := expandChip_extend_honest b orbit (rowNodeSet nodes) chals pubs (cellTemplateHQ δF)
    (atomTemplateHQ δF) 130 205 (cellTemplateHQ_baseCols δF) (atomTemplateHQ_baseCols δF)
    (by omega) (by omega) (by simp only [cellTemplateHQ_extCols, atomTemplateHQ_extCols]; omega)
    (fun g hg => ⟨List.mem_append_left _ hg, by
      have := hB g hg; rwa [cellTemplateHQ_baseCols] at this⟩)
    (fun g hg => ⟨by
        show g ∈ Cell.mixedGates δF ++ CellHQ.gates δF ++ atomMixed δF
        exact List.mem_append_left _ hg, by
      have := hM g hg; rwa [cellTemplateHQ_baseCols, cellTemplateHQ_extCols] at this⟩)
    rfl rfl hn nodes col (newFull δF b hn nodes orbit chals pubs col newB) hsat0 ?_ ?_
  · rw [hW'] at key
    exact key
  · intro x hx g hg hg0
    obtain ⟨i, rfl⟩ := (mem_rowNodeSet_iff nodes x).mp hx
    have hga : g ∈ atomGates (F := F) := by
      have hg' : g ∈ Cell.baseGates ++ atomGates (F := F) := hg
      rcases List.mem_append.mp hg' with h1 | h1
      · exact absurd h1 hg0
      · exact h1
    rw [hWA]
    set e1 := Reify.envOfTrace (honestQ hn nodes (extColF 130 205 ((cellTemplateHQ δF).width 3) col
      (newFull δF b hn nodes orbit chals pubs col newB)) 349) orbit.ω (nodes i) (slotVal b 205 chals)
      (slotVal b 205 pubs) with he1
    have hag : ∀ j, j < 313 → e1.trace j = (EZ δF b hn nodes orbit chals pubs col newB i).trace j ∧
        e1.traceNext j = (EZ δF b hn nodes orbit chals pubs col newB i).traceNext j := by
      intro j hj
      simp only [he1, EZ, Reify.envOfTrace, hWA, dif_pos (show j < 349 by omega)]
      have := hP ⟨j, by omega⟩ hj
      simp only [colA] at this
      rw [this]
      exact ⟨rfl, rfl⟩
    rw [colsBelow_eval (atomGates_below g hga) (fun j hj => (hag j (by omega)).1)
      (fun j hj => (hag j (by omega)).2)]
    exact hbase i g hga
  · intro x hx g hg hg0
    obtain ⟨i, rfl⟩ := (mem_rowNodeSet_iff nodes x).mp hx
    have hgq : g ∈ (atomQ δF).flatMap QE.gates := by
      have hg' : g ∈ Cell.mixedGates δF ++ CellHQ.gates δF ++ atomMixed δF := hg
      rcases List.mem_append.mp hg' with h1 | h1
      · exact absurd h1 hg0
      · exact h1
    rw [hWA]
    obtain ⟨b1, b2, b3, b4, b5, b6⟩ := den_below δF
    have hall : ∀ e ∈ atomQ δF,
        e.ev δF (EK δF b hn nodes orbit chals pubs col newB i) (E1 δF b hn nodes orbit chals pubs col newB i) = 0 := by
      intro e he
      have hsplit : atomQ δF = tripList δF mbInv mbAcc mb pubMB (den δF mbKey) ++
          tripList δF cInv cAcc inc pubC (HQ.denKeyQ δF oldKey) ++
          tripList δF miInv miAcc mi pubMI (HQ.denKeyQ δF incKey) := rfl
      rw [hsplit] at he
      have R := roleValA_re_im δF b hn nodes orbit chals pubs col newB
      rcases List.mem_append.mp he with he | he
      · rcases List.mem_append.mp he with he | he
        · exact atom_block δF b hn nodes orbit chals pubs col newB hinj hadj i mbInv mbAcc mb pubMB _ 0 2 rfl rfl
            (by omega) (by omega) (by simp [mb]) (by simp [mb]) b1 b2 (dMB δF b hn nodes orbit chals pubs col newB) rfl hz1
            (fun i' => ⟨(R i').1.symm, (R i').2.1.symm⟩)
            (fun i' => ⟨(R i').2.2.1.symm, (R i').2.2.2.1.symm⟩) hpMB
            ⟨EK_pub δF b hn nodes orbit chals pubs col newB i _, EK_pub δF b hn nodes orbit chals pubs col newB i _⟩ e he
        · exact atom_block δF b hn nodes orbit chals pubs col newB hinj hadj i cInv cAcc inc pubC _ 4 10 rfl rfl
            (by omega) (by omega) (by simp [inc]) (by simp [inc]) b3 b4 (dC δF b hn nodes orbit chals pubs col newB) rfl hz2
            (fun i' => ⟨(R i').2.2.2.2.1.symm, (R i').2.2.2.2.2.1.symm⟩)
            (fun i' => ⟨(R i').2.2.2.2.2.2.2.2.2.2.1.symm, (R i').2.2.2.2.2.2.2.2.2.2.2.symm⟩) hpC
            ⟨EK_pub δF b hn nodes orbit chals pubs col newB i _, EK_pub δF b hn nodes orbit chals pubs col newB i _⟩ e he
      · exact atom_block δF b hn nodes orbit chals pubs col newB hinj hadj i miInv miAcc mi pubMI _ 6 8 rfl rfl
          (by omega) (by omega) (by simp [mi]) (by simp [mi]) b5 b6 (dMI δF b hn nodes orbit chals pubs col newB) rfl hz3
          (fun i' => ⟨(R i').2.2.2.2.2.2.1.symm, (R i').2.2.2.2.2.2.2.1.symm⟩)
          (fun i' => ⟨(R i').2.2.2.2.2.2.2.2.1.symm, (R i').2.2.2.2.2.2.2.2.2.1.symm⟩) hpMI
          ⟨EK_pub δF b hn nodes orbit chals pubs col newB i _, EK_pub δF b hn nodes orbit chals pubs col newB i _⟩ e he
    exact flat_gates_of_ev δF (atomQ δF) _ _ hall g hgq

end Main2

end

end Nock.NockVMROM.Thm54.VclL.Handle.HonestA8

