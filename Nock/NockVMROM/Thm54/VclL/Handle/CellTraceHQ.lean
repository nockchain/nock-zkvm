/-
  Nock/NockVMROM/Thm54/VclL/Handle/CellTraceHQ.lean

  **`cellTraceHQ`, the honest 238-column `𝕂′` cell twin trace, and
  `cellChipHQ_accepts_honest`** — the (fixed) `cellChipHQ` is satisfiable, under exactly the side
  conditions of `cellChipH_accepts_honest` read at `𝕂′`.  Additive (the `𝕂′` copy of `CellTraceH`).

  `colHQ` extends the honest 225-column cell column function by the multiplicity `mh` (column `129`) and
  the `𝕂′` roles: `invH′` Re / Im at `226..228 / 229..231`, `accH′` Re / Im at `232..234 / 235..237`.
  With the inverse `den′⁻¹`, the accumulator the inclusive prefix sum of `mh · den′⁻¹`, the `𝕂′` public
  the total and no vanishing denominator, the twin accepts it (`expandChip_extend_honest` and
  `cellHQ_gates_honest`, a `QE.ev` computation).
-/
import Nock.NockVMROM.Thm54.VclL.Handle.CellTraceH
import Nock.NockVMROM.Thm54.VclL.Handle.MemHQ

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

/-- A `𝕂′` equation with value `0` has both `𝕂`-gates `0`. -/
theorem gates_of_ev (e : QE F) (eK : Env K) (eF : Env F) (h : e.ev δF eK eF = 0) :
    ∀ g ∈ e.gates, g.eval eK eF = 0 := by
  rw [QE.ev, Quad.mk_eq_zero_iff] at h
  intro g hg
  simp only [QE.gates, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl
  · exact h.1
  · exact h.2

/-- A `QE` gate list holds once every `𝕂′` equation has value `0`. -/
theorem flat_gates_of_ev (L : List (QE F)) (eK : Env K) (eF : Env F)
    (h : ∀ e ∈ L, e.ev δF eK eF = 0) : ∀ g ∈ L.flatMap QE.gates, g.eval eK eF = 0 := by
  intro g hg
  obtain ⟨e, he, hg⟩ := List.mem_flatMap.mp hg
  exact gates_of_ev δF e eK eF (h e he) g hg

theorem liftQ_ite (c : Prop) [Decidable c] :
    liftQ δF (if c then (1 : F) else 0) = if c then (1 : Quad (algebraMap F K δF)) else 0 := by
  split_ifs <;> simp [liftQ]

/-- **The four `𝕂′` cell-twin handle gates at the honest fill** (row `i < N`). -/
theorem cellHQ_gates_honest (eK : Env K) (eF : Env F) (N i : ℕ) (hi : i < N)
    (m : ℕ → F) (d : ℕ → Quad (algebraMap F K δF)) (hd0 : d i ≠ 0)
    (hF : eF.trace Cell.isF = if i = 0 then 1 else 0)
    (hL : eF.trace Cell.isL = if i + 1 = N then 1 else 0)
    (hm : eF.trace CellH.mh = m i) (hmn : i + 1 < N → eF.traceNext CellH.mh = m (i + 1))
    (hden : (HQ.denKeyQ δF (CellH.keyH (F := F))).ev δF eK eF = d i)
    (hinv : Quad.mk _ (eK.trace CellHQ.invHQ) (eK.trace (CellHQ.invHQ + 1)) = (d i)⁻¹)
    (hinvn : i + 1 < N → Quad.mk _ (eK.traceNext CellHQ.invHQ) (eK.traceNext (CellHQ.invHQ + 1)) =
      (d (i + 1))⁻¹)
    (hacc : Quad.mk _ (eK.trace CellHQ.accHQ) (eK.trace (CellHQ.accHQ + 1)) =
      ∑ j ∈ Finset.range (i + 1), liftQ δF (m j) * (d j)⁻¹)
    (haccn : i + 1 < N → Quad.mk _ (eK.traceNext CellHQ.accHQ) (eK.traceNext (CellHQ.accHQ + 1)) =
      ∑ j ∈ Finset.range (i + 2), liftQ δF (m j) * (d j)⁻¹)
    (hpub : Quad.mk _ (eK.pub CellHQ.pubHQ) (eK.pub (CellHQ.pubHQ + 1)) =
      ∑ j ∈ Finset.range N, liftQ δF (m j) * (d j)⁻¹) :
    ∀ g ∈ CellHQ.gates δF, g.eval eK eF = 0 := by
  refine flat_gates_of_ev δF _ eK eF fun e he => ?_
  simp only [CellHQ.gatesQ, List.mem_cons, List.not_mem_nil, or_false] at he
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

end

end QGates

namespace CellTraceHQ

section Data
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [Fintype K]
  (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))] (b : Basis (Fin 3) F K) {n : ℕ}

theorem cellTemplateHQ_width : (cellTemplateHQ δF).width 3 = 238 := by
  unfold ChipTemplate.width; rw [cellTemplateHQ_baseCols, cellTemplateHQ_extCols]

/-- The new `𝕂′` cell-twin columns: `mh` at `129`; Re / Im limbs of `iv` at `226..231`, of `av` at
`232..237`. -/
def new (mhv : Fin n → F) (iv av : Fin n → Quad (algebraMap F K δF)) : ℕ → Fin n → F := fun j i =>
  if j = 129 then mhv i
  else if 226 ≤ j ∧ j < 229 then coordN b (Quad.re _ (iv i)) (j - 226)
  else if 229 ≤ j ∧ j < 232 then coordN b (Quad.im _ (iv i)) (j - 229)
  else if 232 ≤ j ∧ j < 235 then coordN b (Quad.re _ (av i)) (j - 232)
  else if 235 ≤ j ∧ j < 238 then coordN b (Quad.im _ (av i)) (j - 235) else 0

/-- **`cellTraceHQ`'s column function**: the honest original columns plus the new ones. -/
def colHQ (col : ℕ → Fin n → F) (mhv : Fin n → F) (iv av : Fin n → Quad (algebraMap F K δF)) :
    ℕ → Fin n → F :=
  extColF 129 130 ((cellTemplate δF).width 3) col (new δF b mhv iv av)

end Data

section Rows
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [Fintype K]
  (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))] (b : Basis (Fin 3) F K) {h n : ℕ} (hn : 0 < n)
  (nodes : Fin n → F) (orbit : StrictOrbitDomain F 3 h) (chals pubs : ℕ → K)

def E (col : ℕ → Fin n → F) (mhv : Fin n → F) (iv av : Fin n → Quad (algebraMap F K δF)) (i : Fin n) :
    Env F :=
  Reify.envOfTrace (honestQ hn nodes (colHQ δF b col mhv iv av) ((cellTemplateHQ δF).width 3))
    orbit.ω (nodes i) (slotVal b 130 chals) (slotVal b 130 pubs)

/-- The `𝕂′` denominator of row `i`'s export key (zero role fill: it reads base columns only). -/
def dRow (col : ℕ → Fin n → F) (mhv : Fin n → F) (i : Fin n) : Quad (algebraMap F K δF) :=
  (HQ.denKeyQ δF (CellH.keyH (F := F))).ev δF
    (gatherEnv b ((cellTemplateHQ δF).col0 3) (E δF b hn nodes orbit chals pubs col mhv (fun _ => 0) (fun _ => 0) i))
    (E δF b hn nodes orbit chals pubs col mhv (fun _ => 0) (fun _ => 0) i)

end Rows

section Facts
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [Fintype K]
  (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))] (b : Basis (Fin 3) F K) {h n : ℕ} (hn : 0 < n)
  (nodes : Fin n → F) (orbit : StrictOrbitDomain F 3 h) (chals pubs : ℕ → K)
  (col : ℕ → Fin n → F) (mhv : Fin n → F) (iv av : Fin n → Quad (algebraMap F K δF))

theorem colHQ_lt130 (j : ℕ) (hj : j < 130) (iv' av' : Fin n → Quad (algebraMap F K δF)) :
    colHQ δF b col mhv iv av j = colHQ δF b col mhv iv' av' j := by
  funext i
  simp only [colHQ, extColF, new]
  by_cases h1 : j < 129
  · simp [h1]
  · have : j = 129 := by omega
    subst this; simp

theorem E_below (iv' av' : Fin n → Quad (algebraMap F K δF)) (i : Fin n) (j : ℕ) (hj : j < 130) :
    (E δF b hn nodes orbit chals pubs col mhv iv av i).trace j =
        (E δF b hn nodes orbit chals pubs col mhv iv' av' i).trace j ∧
    (E δF b hn nodes orbit chals pubs col mhv iv av i).traceNext j =
        (E δF b hn nodes orbit chals pubs col mhv iv' av' i).traceNext j := by
  have hw : j < (cellTemplateHQ δF).width 3 := by rw [cellTemplateHQ_width]; omega
  have hq := honestQ_congr hn nodes (colHQ δF b col mhv iv av) (colHQ δF b col mhv iv' av')
    ((cellTemplateHQ δF).width 3) ⟨j, hw⟩ (colHQ_lt130 δF b col mhv iv av j hj iv' av')
  simp [E, Reify.envOfTrace, dif_pos hw, hq]

theorem gather_chal (e : Env F) (hc : e.chal = slotVal b 130 chals) (r : ℕ) :
    (gatherEnv b ((cellTemplateHQ δF).col0 3) e).chal r = chals r := by
  simp only [gatherEnv, ChipTemplate.col0, hc, cellTemplateHQ_baseCols]
  exact sum_slotVal b 130 r chals

theorem gather_pub (e : Env F) (hc : e.pub = slotVal b 130 pubs) (r : ℕ) :
    (gatherEnv b ((cellTemplateHQ δF).col0 3) e).pub r = pubs r := by
  simp only [gatherEnv, ChipTemplate.col0, hc, cellTemplateHQ_baseCols]
  exact sum_slotVal b 130 r pubs

/-- `γH′^m` reads the coins only. -/
theorem gpowQ_congr (eK eK' : Env K) (eF eF' : Env F) (hc : eK.chal = eK'.chal) :
    ∀ m, (HQ.gpowQ δF m).ev δF eK eF = (HQ.gpowQ δF m).ev δF eK' eF'
  | 0 => by simp [HQ.gpowQ, ev_one]
  | m + 1 => by
      simp only [HQ.gpowQ, ev_mul, HQ.gamQ, ev_chal, hc, gpowQ_congr eK eK' eF eF' hc m]

theorem rlcQ_congr (eK eK' : Env K) (eF eF' : Env F) (hc : eK.chal = eK'.chal)
    (ht : ∀ j < 130, eF.trace j = eF'.trace j) (hn : ∀ j < 130, eF.traceNext j = eF'.traceNext j) :
    ∀ (l : List (CoeffExpr F)), (∀ g ∈ l, colsBelow 130 g = true) → ∀ m,
      (HQ.rlcQ δF m l).ev δF eK eF = (HQ.rlcQ δF m l).ev δF eK' eF'
  | [], _, m => by simp [HQ.rlcQ, ev_zero]
  | g :: r, hl, m => by
      simp only [HQ.rlcQ, ev_add, ev_mul, ev_base, gpowQ_congr δF eK eK' eF eF' hc m,
        colsBelow_eval (hl g (by simp)) ht hn,
        rlcQ_congr eK eK' eF eF' hc ht hn r (fun g' hg' => hl g' (by simp [hg'])) (m + 1)]

theorem keyH_below130 : ∀ g ∈ (CellH.keyH (F := F)), colsBelow 130 g = true := by
  intro g hg
  have := CellTraceH.keyH_below g hg
  exact this

/-- The `𝕂′` denominator reads only base columns below `130` and the coins. -/
theorem denKeyQ_congr (e e' : Env F) (hc : e.chal = slotVal b 130 chals) (hc' : e'.chal = slotVal b 130 chals)
    (ht : ∀ j < 130, e.trace j = e'.trace j) (hn : ∀ j < 130, e.traceNext j = e'.traceNext j) :
    (HQ.denKeyQ δF (CellH.keyH (F := F))).ev δF (gatherEnv b ((cellTemplateHQ δF).col0 3) e) e =
      (HQ.denKeyQ δF (CellH.keyH (F := F))).ev δF (gatherEnv b ((cellTemplateHQ δF).col0 3) e') e' := by
  have hcc : (gatherEnv b ((cellTemplateHQ δF).col0 3) e).chal =
      (gatherEnv b ((cellTemplateHQ δF).col0 3) e').chal := by
    funext r; rw [gather_chal δF b chals e hc, gather_chal δF b chals e' hc']
  simp only [HQ.denKeyQ, ev_add, HQ.rhoQ, ev_chal, hcc,
    rlcQ_congr δF _ _ e e' hcc ht hn _ keyH_below130 0]

theorem den_indep (i : Fin n) :
    (HQ.denKeyQ δF (CellH.keyH (F := F))).ev δF
      (gatherEnv b ((cellTemplateHQ δF).col0 3) (E δF b hn nodes orbit chals pubs col mhv iv av i))
      (E δF b hn nodes orbit chals pubs col mhv iv av i) = dRow δF b hn nodes orbit chals pubs col mhv i :=
  denKeyQ_congr δF b chals _ _ rfl rfl
    (fun j hj => (E_below δF b hn nodes orbit chals pubs col mhv iv av (fun _ => 0) (fun _ => 0) i j hj).1)
    (fun j hj => (E_below δF b hn nodes orbit chals pubs col mhv iv av (fun _ => 0) (fun _ => 0) i j hj).2)

end Facts

section Main
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [Fintype K]
  (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))] (b : Basis (Fin 3) F K) {h n : ℕ} (hn : 0 < n)
  (nodes : Fin n → F) (orbit : StrictOrbitDomain F 3 h) (chals pubs : ℕ → K)
  (col : ℕ → Fin n → F) (mhv : Fin n → F)

def dN (j : ℕ) : Quad (algebraMap F K δF) :=
  if hj : j < n then dRow δF b hn nodes orbit chals pubs col mhv ⟨j, hj⟩ else 1

/-- **The honest `𝕂′` inverse fill**: `invH′ = den′⁻¹`. -/
def ivF : Fin n → Quad (algebraMap F K δF) := fun i => (dRow δF b hn nodes orbit chals pubs col mhv i)⁻¹
/-- **The honest `𝕂′` accumulator fill**: the inclusive prefix sum of `mh · den′⁻¹`. -/
def avF : Fin n → Quad (algebraMap F K δF) := fun i =>
  ∑ j ∈ Finset.range (i + 1), liftQ δF (CellTraceH.mN mhv j) * (dN δF b hn nodes orbit chals pubs col mhv j)⁻¹

/-- **`cellTraceHQ`**: the honest 238-column `𝕂′` cell twin trace. -/
def cellTraceHQ :=
  honestQ hn nodes (colHQ δF b col mhv (ivF δF b hn nodes orbit chals pubs col mhv)
    (avF δF b hn nodes orbit chals pubs col mhv)) ((cellTemplateHQ δF).width 3)

theorem coordN_shift (v : K) (j c : ℕ) (k : Fin 3) (hj : j = c + k) :
    coordN b v (j - c) = coord b v k := by
  rw [show j - c = k by omega]; exact coordN_eq b _ k

/-- **The `𝕂′` cell twin accepts `cellTraceHQ`**, from the original honest cell acceptance, no
vanishing `𝕂′` denominator and the `𝕂′` public equal to the total. -/
theorem cellChipHQ_accepts_honest (hinj : Function.Injective nodes)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω)
    (hsat0 : (cellChip δF b hn nodes orbit chals pubs).rap.Satisfies (honestQ hn nodes col _))
    (hpole : ∀ i, dRow δF b hn nodes orbit chals pubs col mhv i ≠ 0)
    (hpub : Quad.mk _ (pubs CellHQ.pubHQ) (pubs (CellHQ.pubHQ + 1)) = ∑ j ∈ Finset.range n,
      liftQ δF (CellTraceH.mN mhv j) * (dN δF b hn nodes orbit chals pubs col mhv j)⁻¹) :
    (cellChipHQ δF b hn nodes orbit chals pubs).rap.Satisfies
      (cellTraceHQ δF b hn nodes orbit chals pubs col mhv) := by
  have hW' : (cellTemplateHQ δF).width 3 = 238 := cellTemplateHQ_width δF
  have hW : (cellTemplate δF).width 3 = 225 := CellTraceH.cellTemplate_width δF
  have hR : (cellTemplate δF).extCols = 32 := cellTemplate_extCols δF
  refine expandChip_extend_honest b orbit (rowNodeSet nodes) chals pubs (cellTemplate δF)
    (cellTemplateHQ δF) 129 130 (cellTemplate_baseCols δF) (cellTemplateHQ_baseCols δF) (by omega)
    (by omega) (by rw [hR, cellTemplateHQ_extCols]; omega)
    (fun g hg => ⟨hg, cellBase_below g hg⟩)
    (fun g hg => ⟨List.mem_append_left _ hg, by rw [hR]; exact cellMixed_below δF g hg⟩)
    rfl rfl hn nodes col (new δF b mhv (ivF δF b hn nodes orbit chals pubs col mhv)
      (avF δF b hn nodes orbit chals pubs col mhv)) hsat0
    (fun x hx g hg hg0 => absurd hg hg0) ?_
  intro x hx g hg hg0
  obtain ⟨i, rfl⟩ := (mem_rowNodeSet_iff nodes x).mp hx
  have hgm : g ∈ CellHQ.gates δF := by
    have hg' : g ∈ Cell.mixedGates δF ++ CellHQ.gates δF := hg
    rcases List.mem_append.mp hg' with h1 | h1
    · exact absurd h1 hg0
    · exact h1
  set iv := ivF δF b hn nodes orbit chals pubs col mhv
  set av := avF δF b hn nodes orbit chals pubs col mhv
  have hE : Reify.envOfTrace (honestQ hn nodes (extColF 129 130 ((cellTemplate δF).width 3) col
      (new δF b mhv iv av)) ((cellTemplateHQ δF).width 3)) orbit.ω (nodes i) (slotVal b 130 chals)
      (slotVal b 130 pubs) = E δF b hn nodes orbit chals pubs col mhv iv av i := rfl
  rw [hE]
  set e1 := E δF b hn nodes orbit chals pubs col mhv iv av i with he1
  have hwlt : ∀ j, j < 238 → j < (cellTemplateHQ δF).width 3 := fun j hj => by omega
  have hET : ∀ j, j < 238 → e1.trace j = fullCol hn (colHQ δF b col mhv iv av) j i := fun j hj =>
    env_trace hn nodes hinj _ _ _ _ i (hwlt j hj)
  have hENx : ∀ (hi : (i : ℕ) + 1 < n) j, j < 238 →
      e1.traceNext j = fullCol hn (colHQ δF b col mhv iv av) j ⟨(i : ℕ) + 1, hi⟩ := fun hi j hj =>
    env_traceNext hn nodes hinj _ _ _ _ hadj i hi (hwlt j hj)
  have hnew : ∀ j, 2 ≤ j → fullCol hn (colHQ δF b col mhv iv av) j = colHQ δF b col mhv iv av j := by
    intro j hj; funext i'; simp only [fullCol]; split_ifs <;> first | omega | rfl
  have hcol0 : ∀ r k : ℕ, (cellTemplateHQ δF).col0 3 .traceCur r + k = 130 + 3 * r + k := by
    intro r k; simp only [ChipTemplate.col0, cellTemplateHQ_baseCols]
  have hcolN : ∀ r k : ℕ, (cellTemplateHQ δF).col0 3 .traceNext r + k = 130 + 3 * r + k := hcol0
  -- the four role groups
  have hlimb : ∀ (i' : Fin n) (c : ℕ) (k : Fin 3), 226 ≤ c → c + 3 ≤ 238 → c % 3 = 1 →
      fullCol hn (colHQ δF b col mhv iv av) (c + k) i' =
        coord b (if c = 226 then Quad.re _ (iv i') else if c = 229 then Quad.im _ (iv i')
          else if c = 232 then Quad.re _ (av i') else Quad.im _ (av i')) k := by
    intro i' c k h1 h2 h3
    have hk := k.isLt
    rw [hnew _ (by omega)]
    simp only [colHQ, extColF, new, hW]
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    have hc : c = 226 ∨ c = 229 ∨ c = 232 ∨ c = 235 := by omega
    rcases hc with rfl | rfl | rfl | rfl
    · rw [if_pos ⟨by omega, by omega⟩, if_pos rfl]; exact coordN_shift b _ _ _ k rfl
    · rw [if_neg (by omega), if_pos ⟨by omega, by omega⟩, if_neg (by omega), if_pos rfl]
      exact coordN_shift b _ _ _ k rfl
    · rw [if_neg (by omega), if_neg (by omega), if_pos ⟨by omega, by omega⟩, if_neg (by omega),
        if_neg (by omega), if_pos rfl]
      exact coordN_shift b _ _ _ k rfl
    · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos ⟨by omega, by omega⟩,
        if_neg (by omega), if_neg (by omega), if_neg (by omega)]
      exact coordN_shift b _ _ _ k rfl
  have hmh : ∀ i' : Fin n, fullCol hn (colHQ δF b col mhv iv av) 129 i' = mhv i' := by
    intro i'
    rw [hnew _ (by omega)]
    simp only [colHQ, extColF, new]
    rw [if_neg (by omega), if_pos (by omega)]; simp
  have hd : ∀ i' : Fin n, dN δF b hn nodes orbit chals pubs col mhv i' =
      dRow δF b hn nodes orbit chals pubs col mhv i' := fun i' => by simp [dN]
  set eK := gatherEnv b ((cellTemplateHQ δF).col0 3) e1 with heK
  have hrole : ∀ (r c : ℕ) (v : K), 130 + 3 * r = c → 226 ≤ c → c + 3 ≤ 238 → c % 3 = 1 →
      (∀ k : Fin 3, fullCol hn (colHQ δF b col mhv iv av) (c + k) i = coord b v k) → eK.trace r = v := by
    intro r c v hrc h1 h2 _ hv
    refine gather_trace b _ e1 r v fun k => ?_
    rw [hcol0, hrc, hET _ (by have := k.isLt; omega)]; exact hv k
  have hroleN : ∀ (hi : (i : ℕ) + 1 < n) (r c : ℕ) (v : K), 130 + 3 * r = c → 226 ≤ c → c + 3 ≤ 238 →
      c % 3 = 1 → (∀ k : Fin 3, fullCol hn (colHQ δF b col mhv iv av) (c + k) ⟨(i : ℕ) + 1, hi⟩ = coord b v k) →
      eK.traceNext r = v := by
    intro hi r c v hrc h1 h2 _ hv
    refine gather_traceNext b _ e1 r v fun k => ?_
    rw [hcolN, hrc, hENx hi _ (by have := k.isLt; omega)]; exact hv k
  have hinvQ : ∀ (i' : Fin n), iv i' = (dN δF b hn nodes orbit chals pubs col mhv i')⁻¹ := fun i' => by
    simp [iv, ivF, hd]
  refine QGates.cellHQ_gates_honest δF eK e1 n i i.isLt
    (CellTraceH.mN mhv) (dN δF b hn nodes orbit chals pubs col mhv) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ g hgm
  · rw [hd]; exact hpole i
  · show e1.trace 0 = _
    rw [hET 0 (by omega)]; simp [fullCol]
  · show e1.trace 1 = _
    rw [hET 1 (by omega)]
    simp only [fullCol, one_ne_zero, if_false, if_true]
    by_cases hl : (i : ℕ) + 1 = n
    · rw [if_pos hl, if_pos]; exact Fin.ext (by simp; omega)
    · rw [if_neg hl, if_neg]; intro hh; apply hl; have := congrArg Fin.val hh; simp at this; omega
  · show e1.trace 129 = _
    rw [hET 129 (by omega), hmh]; simp [CellTraceH.mN]
  · intro hi; show e1.traceNext 129 = _
    rw [hENx hi 129 (by omega), hmh]; simp [CellTraceH.mN, hi]
  · rw [hd]; exact (den_indep δF b hn nodes orbit chals pubs col mhv iv av i).trans (by simp [dN])
  · show Quad.mk _ (eK.trace 32) (eK.trace 33) = _
    rw [hrole 32 226 (Quad.re _ (iv i)) (by decide) le_rfl (by omega) (by decide) (fun k => by
        rw [hlimb i 226 k le_rfl (by omega) (by decide)]; try simp),
      hrole 33 229 (Quad.im _ (iv i)) (by decide) (by omega) (by omega) (by decide) (fun k => by
        rw [hlimb i 229 k (by omega) (by omega) (by decide)]; try simp),
      Quad.mk_re_im, hinvQ]
  · intro hi
    show Quad.mk _ (eK.traceNext 32) (eK.traceNext 33) = _
    rw [hroleN hi 32 226 (Quad.re _ (iv ⟨(i : ℕ) + 1, hi⟩)) (by decide) le_rfl (by omega) (by decide) (fun k => by
        rw [hlimb _ 226 k le_rfl (by omega) (by decide)]; try simp),
      hroleN hi 33 229 (Quad.im _ (iv ⟨(i : ℕ) + 1, hi⟩)) (by decide) (by omega) (by omega) (by decide) (fun k => by
        rw [hlimb _ 229 k (by omega) (by omega) (by decide)]; try simp),
      Quad.mk_re_im, hinvQ]
  · show Quad.mk _ (eK.trace 34) (eK.trace 35) = _
    rw [hrole 34 232 (Quad.re _ (av i)) (by decide) (by omega) (by omega) (by decide) (fun k => by
        rw [hlimb i 232 k (by omega) (by omega) (by decide)]; try simp),
      hrole 35 235 (Quad.im _ (av i)) (by decide) (by omega) (by omega) (by decide) (fun k => by
        rw [hlimb i 235 k (by omega) (by omega) (by decide)]; try simp),
      Quad.mk_re_im]
    rfl
  · intro hi
    show Quad.mk _ (eK.traceNext 34) (eK.traceNext 35) = _
    rw [hroleN hi 34 232 (Quad.re _ (av ⟨(i : ℕ) + 1, hi⟩)) (by decide) (by omega) (by omega) (by decide) (fun k => by
        rw [hlimb _ 232 k (by omega) (by omega) (by decide)]; try simp),
      hroleN hi 35 235 (Quad.im _ (av ⟨(i : ℕ) + 1, hi⟩)) (by decide) (by omega) (by omega) (by decide) (fun k => by
        rw [hlimb _ 235 k (by omega) (by omega) (by decide)]; try simp),
      Quad.mk_re_im]
    rfl
  · rw [← hpub]
    congr 1
    · simp only [heK, gatherEnv, ChipTemplate.col0, cellTemplateHQ_baseCols]
      exact sum_slotVal b 130 CellHQ.pubHQ pubs
    · simp only [heK, gatherEnv, ChipTemplate.col0, cellTemplateHQ_baseCols]
      exact sum_slotVal b 130 (CellHQ.pubHQ + 1) pubs

end Main

end CellTraceHQ

end

end Nock.NockVMROM.Thm54.VclL.Handle
