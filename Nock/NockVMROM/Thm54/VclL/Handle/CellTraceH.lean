/-
  Nock/NockVMROM/Thm54/VclL/Handle/CellTraceH.lean

  Additive.

  `cellColH` extends the honest 225-column cell column function `col` by the multiplicity `mh`
  (column `129`) and the two `𝕂`-roles `invH` (`32`, columns `226..228`) and `accH` (`33`,
  columns `229..231`).  `cellChipH_accepts_honest`: with the inverse fill `invH = den⁻¹`, the
  accumulator the inclusive prefix sum of `mh · den⁻¹`, the public the total, no vanishing
  denominator, the twin accepts it, through `expandChip_extend_honest` and `cellH_gates_honest`.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.ExtendH
import Nock.NockVMROM.Thm54.VclL.Handle.TwinGatesH

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.NockVMROM.Thm54.VclL.Handle

open Nock Nock.Reified Nock.Framework
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Module
open scoped Polynomial

noncomputable section

section Common
variable {F K : Type} [Field F] [Field K] [Algebra F K]

/-- Coordinate `k % 3` of `v` (total in `k`, so the new-column functions need no bound proofs). -/
def coordN (b : Basis (Fin 3) F K) (v : K) (k : ℕ) : F :=
  coord b v ⟨k % 3, Nat.mod_lt _ (by norm_num)⟩

theorem coordN_eq (b : Basis (Fin 3) F K) (v : K) (k : Fin 3) : coordN b v k = coord b v k := by
  unfold coordN
  congr 1
  exact Fin.ext (Nat.mod_eq_of_lt k.isLt)

theorem mem_rowNodeSet_iff {n : ℕ} (nodes : Fin n → F) (x : F) :
    x ∈ rowNodeSet nodes ↔ ∃ i, nodes i = x := by
  classical
  unfold rowNodeSet
  simp

end Common

namespace CellTraceH

section Data
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
  (δF : F) (b : Basis (Fin 3) F K) {n : ℕ}

theorem cellTemplate_width (δF : F) : (cellTemplate δF).width 3 = 225 := by
  unfold ChipTemplate.width; rw [cellTemplate_baseCols, cellTemplate_extCols]
theorem cellTemplateH_width (δF : F) : (cellTemplateH δF).width 3 = 232 := by
  unfold ChipTemplate.width; rw [cellTemplateH_baseCols, cellTemplateH_extCols]

/-- The new cell-twin columns: `mh` at `129`; limbs of `iv` at `226..228`, of `av` at `229..231`. -/
def new (mhv : Fin n → F) (iv av : Fin n → K) : ℕ → Fin n → F := fun j i =>
  if j = 129 then mhv i
  else if 226 ≤ j ∧ j < 229 then coordN b (iv i) (j - 226)
  else if 229 ≤ j ∧ j < 232 then coordN b (av i) (j - 229) else 0

/-- **`cellTraceH`'s column function**: the honest original columns plus the new ones. -/
def colH (col : ℕ → Fin n → F) (mhv : Fin n → F) (iv av : Fin n → K) : ℕ → Fin n → F :=
  extColF 129 130 ((cellTemplate δF).width 3) col (new b mhv iv av)

end Data

section Rows
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
  (δF : F) (b : Basis (Fin 3) F K) {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F)
  (orbit : StrictOrbitDomain F 3 h) (chals pubs : ℕ → K)

/-- Row `i`'s base environment of the honest twin trace. -/
def E (col : ℕ → Fin n → F) (mhv : Fin n → F) (iv av : Fin n → K) (i : Fin n) : Env F :=
  Reify.envOfTrace (honestQ hn nodes (colH δF b col mhv iv av) ((cellTemplateH δF).width 3))
    orbit.ω (nodes i) (slotVal b 130 chals) (slotVal b 130 pubs)

/-- The denominator of row `i`'s export key, read off the twin environment (with a zero role fill:
the denominator reads only base columns, `den_indep`). -/
def dRow (col : ℕ → Fin n → F) (mhv : Fin n → F) (i : Fin n) : K :=
  (CellH.denKey (CellH.keyH (F := F))).eval
    (gatherEnv b ((cellTemplateH δF).col0 3) (E δF b hn nodes orbit chals pubs col mhv (fun _ => 0) (fun _ => 0) i))
    (E δF b hn nodes orbit chals pubs col mhv (fun _ => 0) (fun _ => 0) i)

end Rows


section Facts
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
  (δF : F) (b : Basis (Fin 3) F K) {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F)
  (orbit : StrictOrbitDomain F 3 h) (chals pubs : ℕ → K)
  (col : ℕ → Fin n → F) (mhv : Fin n → F) (iv av : Fin n → K)

theorem keyH_below : ∀ g ∈ (CellH.keyH (F := F)), colsBelow 130 g = true := by
  intro g hg
  simp only [CellH.keyH, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl <;>
    simp [colsBelow, CellH.valE, cv, notE, Cell.idx, Cell.wL, Cell.wR, Cell.idL, Cell.idR, Cell.aL,
      Cell.aR]

theorem colH_lt130 (j : ℕ) (hj : j < 130) (iv' av' : Fin n → K) :
    colH δF b col mhv iv av j = colH δF b col mhv iv' av' j := by
  funext i
  simp only [colH, extColF, new]
  by_cases h1 : j < 129
  · simp [h1]
  · have : j = 129 := by omega
    subst this; simp

theorem E_below (iv' av' : Fin n → K) (i : Fin n) (j : ℕ) (hj : j < 130) :
    (E δF b hn nodes orbit chals pubs col mhv iv av i).trace j =
        (E δF b hn nodes orbit chals pubs col mhv iv' av' i).trace j ∧
    (E δF b hn nodes orbit chals pubs col mhv iv av i).traceNext j =
        (E δF b hn nodes orbit chals pubs col mhv iv' av' i).traceNext j := by
  have hw : j < (cellTemplateH δF).width 3 := by rw [cellTemplateH_width]; omega
  have hq := honestQ_congr hn nodes (colH δF b col mhv iv av) (colH δF b col mhv iv' av')
    ((cellTemplateH δF).width 3) ⟨j, hw⟩ (colH_lt130 δF b col mhv iv av j hj iv' av')
  simp [E, Reify.envOfTrace, dif_pos hw, hq]

theorem gather_chal (e : Env F) (hc : e.chal = slotVal b 130 chals) (r : ℕ) :
    (gatherEnv b ((cellTemplateH δF).col0 3) e).chal r = chals r := by
  simp only [gatherEnv, ChipTemplate.col0, hc, cellTemplateH_baseCols]
  exact sum_slotVal b 130 r chals

theorem gather_pub (e : Env F) (hc : e.pub = slotVal b 130 pubs) (r : ℕ) :
    (gatherEnv b ((cellTemplateH δF).col0 3) e).pub r = pubs r := by
  simp only [gatherEnv, ChipTemplate.col0, hc, cellTemplateH_baseCols]
  exact sum_slotVal b 130 r pubs

/-- The denominator reads only base columns below `130` and the coins. -/
theorem denKey_congr (e e' : Env F) (hc : e.chal = slotVal b 130 chals) (hc' : e'.chal = slotVal b 130 chals)
    (ht : ∀ j < 130, e.trace j = e'.trace j) (hn : ∀ j < 130, e.traceNext j = e'.traceNext j) :
    (CellH.denKey (CellH.keyH (F := F))).eval (gatherEnv b ((cellTemplateH δF).col0 3) e) e =
      (CellH.denKey (CellH.keyH (F := F))).eval (gatherEnv b ((cellTemplateH δF).col0 3) e') e' := by
  rw [denKey_eval, denKey_eval, gather_chal δF b chals e hc, gather_chal δF b chals e hc,
    gather_chal δF b chals e' hc', gather_chal δF b chals e' hc']
  have hm : ((CellH.keyH (F := F)).zipIdx 0).map
        (fun p : CoeffExpr F × ℕ => chals CellH.hGam ^ p.2 * algebraMap F K (p.1.eval e)) =
      ((CellH.keyH (F := F)).zipIdx 0).map
        (fun p : CoeffExpr F × ℕ => chals CellH.hGam ^ p.2 * algebraMap F K (p.1.eval e')) := by
    refine List.map_congr_left fun p hp => ?_
    rw [colsBelow_eval (keyH_below p.1 (List.fst_mem_of_mem_zipIdx hp)) ht hn]
  rw [hm]

theorem den_indep (i : Fin n) :
    (CellH.denKey (CellH.keyH (F := F))).eval
      (gatherEnv b ((cellTemplateH δF).col0 3) (E δF b hn nodes orbit chals pubs col mhv iv av i))
      (E δF b hn nodes orbit chals pubs col mhv iv av i) = dRow δF b hn nodes orbit chals pubs col mhv i :=
  denKey_congr δF b chals _ _ rfl rfl
    (fun j hj => (E_below δF b hn nodes orbit chals pubs col mhv iv av (fun _ => 0) (fun _ => 0) i j hj).1)
    (fun j hj => (E_below δF b hn nodes orbit chals pubs col mhv iv av (fun _ => 0) (fun _ => 0) i j hj).2)

end Facts


section Main
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
  (δF : F) (b : Basis (Fin 3) F K) {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F)
  (orbit : StrictOrbitDomain F 3 h) (chals pubs : ℕ → K)
  (col : ℕ → Fin n → F) (mhv : Fin n → F)

/-- ℕ-indexed multiplicity / denominator (padding off the table). -/
def mN (mhv : Fin n → F) (j : ℕ) : F := if hj : j < n then mhv ⟨j, hj⟩ else 0
def dN (j : ℕ) : K := if hj : j < n then dRow δF b hn nodes orbit chals pubs col mhv ⟨j, hj⟩ else 1

/-- **The honest inverse fill**: `invH = den⁻¹`. -/
def ivF : Fin n → K := fun i => (dRow δF b hn nodes orbit chals pubs col mhv i)⁻¹
/-- **The honest accumulator fill**: the inclusive prefix sum of `mh · den⁻¹`. -/
def avF : Fin n → K := fun i =>
  ∑ j ∈ Finset.range (i + 1), algebraMap F K (mN mhv j) * (dN δF b hn nodes orbit chals pubs col mhv j)⁻¹

/-- **`cellTraceH`**: the honest 232-column cell twin trace. -/
def cellTraceH :=
  honestQ hn nodes (colH δF b col mhv (ivF δF b hn nodes orbit chals pubs col mhv)
    (avF δF b hn nodes orbit chals pubs col mhv)) ((cellTemplateH δF).width 3)

/-- **The cell twin accepts `cellTraceH`.**  From the original honest cell acceptance `hsat0`,
no vanishing denominator (the priced pole event) and the public equal to the total. -/
theorem cellChipH_accepts_honest (hinj : Function.Injective nodes)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω)
    (hsat0 : (cellChip δF b hn nodes orbit chals pubs).rap.Satisfies (honestQ hn nodes col _))
    (hpole : ∀ i, dRow δF b hn nodes orbit chals pubs col mhv i ≠ 0)
    (hpub : pubs CellH.pubH = ∑ j ∈ Finset.range n,
      algebraMap F K (mN mhv j) * (dN δF b hn nodes orbit chals pubs col mhv j)⁻¹) :
    (cellChipH δF b hn nodes orbit chals pubs).rap.Satisfies
      (cellTraceH δF b hn nodes orbit chals pubs col mhv) := by
  have hW : (cellTemplate δF).width 3 = 225 := cellTemplate_width δF
  have hW' : (cellTemplateH δF).width 3 = 232 := cellTemplateH_width δF
  refine expandChip_extend_honest b orbit (rowNodeSet nodes) chals pubs (cellTemplate δF)
    (cellTemplateH δF) 129 130 (cellTemplate_baseCols δF) (cellTemplateH_baseCols δF) (by omega)
    (by omega) (by rw [cellTemplate_extCols, cellTemplateH_extCols]; omega)
    (fun g hg => ⟨hg, cellBase_below g hg⟩)
    (fun g hg => ⟨List.mem_append_left _ hg, by rw [cellTemplate_extCols]; exact cellMixed_below δF g hg⟩)
    rfl rfl hn nodes col (new b mhv (ivF δF b hn nodes orbit chals pubs col mhv)
      (avF δF b hn nodes orbit chals pubs col mhv)) hsat0
    (fun x hx g hg hg0 => absurd hg hg0) ?_
  intro x hx g hg hg0
  obtain ⟨i, rfl⟩ := (mem_rowNodeSet_iff nodes x).mp hx
  have hgm : g ∈ CellH.gates (F := F) := by
    have hg' : g ∈ Cell.mixedGates δF ++ CellH.gates (F := F) := hg
    rcases List.mem_append.mp hg' with h1 | h1
    · exact absurd h1 hg0
    · exact h1
  set iv := ivF δF b hn nodes orbit chals pubs col mhv
  set av := avF δF b hn nodes orbit chals pubs col mhv
  have hE : Reify.envOfTrace (honestQ hn nodes (extColF 129 130 ((cellTemplate δF).width 3) col (new b mhv iv av))
      ((cellTemplateH δF).width 3)) orbit.ω (nodes i) (slotVal b 130 chals) (slotVal b 130 pubs) =
      E δF b hn nodes orbit chals pubs col mhv iv av i := rfl
  rw [hE]
  set e1 := E δF b hn nodes orbit chals pubs col mhv iv av i with he1
  have hwlt : ∀ j, j < 232 → j < (cellTemplateH δF).width 3 := fun j hj => by omega
  have hET : ∀ j, j < 232 → e1.trace j = fullCol hn (colH δF b col mhv iv av) j i := fun j hj =>
    env_trace hn nodes hinj _ _ _ _ i (hwlt j hj)
  have hENx : ∀ (hi : (i : ℕ) + 1 < n) j, j < 232 →
      e1.traceNext j = fullCol hn (colH δF b col mhv iv av) j ⟨(i : ℕ) + 1, hi⟩ := fun hi j hj =>
    env_traceNext hn nodes hinj _ _ _ _ hadj i hi (hwlt j hj)
  have hnew : ∀ j, 2 ≤ j → fullCol hn (colH δF b col mhv iv av) j = colH δF b col mhv iv av j := by
    intro j hj; funext i'; simp only [fullCol]; split_ifs <;> first | omega | rfl
  -- the `𝕂`-role values
  have hcol0 : ∀ r k : ℕ, (cellTemplateH δF).col0 3 .traceCur r + k = 130 + 3 * r + k := by
    intro r k; simp only [ChipTemplate.col0, cellTemplateH_baseCols]
  have hcolN : ∀ r k : ℕ, (cellTemplateH δF).col0 3 .traceNext r + k = 130 + 3 * r + k := hcol0
  have hlimbI : ∀ (i' : Fin n) (k : Fin 3), fullCol hn (colH δF b col mhv iv av) (226 + k) i' =
      coord b (iv i') k := by
    intro i' k
    have hk := k.isLt
    rw [hnew _ (by omega)]
    simp only [colH, extColF, new, hW]
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
      if_pos ⟨by omega, by omega⟩]
    rw [show 226 + (k : ℕ) - 226 = k by omega]; exact coordN_eq b _ k
  have hlimbA : ∀ (i' : Fin n) (k : Fin 3), fullCol hn (colH δF b col mhv iv av) (229 + k) i' =
      coord b (av i') k := by
    intro i' k
    have hk := k.isLt
    rw [hnew _ (by omega)]
    simp only [colH, extColF, new, hW]
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
      if_neg (by omega), if_pos ⟨by omega, by omega⟩]
    rw [show 229 + (k : ℕ) - 229 = k by omega]; exact coordN_eq b _ k
  have hmh : ∀ i' : Fin n, fullCol hn (colH δF b col mhv iv av) 129 i' = mhv i' := by
    intro i'
    rw [hnew _ (by omega)]
    simp only [colH, extColF, new]
    rw [if_neg (by omega), if_pos (by omega)]; simp
  have hd : ∀ i' : Fin n, dN δF b hn nodes orbit chals pubs col mhv i' =
      dRow δF b hn nodes orbit chals pubs col mhv i' := fun i' => by simp [dN]
  refine cellH_gates_honest (gatherEnv b ((cellTemplateH δF).col0 3) e1) e1 n i i.isLt
    (mN mhv) (dN δF b hn nodes orbit chals pubs col mhv) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ g hgm
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
    rw [hET 129 (by omega), hmh]; simp [mN]
  · intro hi; show e1.traceNext 129 = _
    rw [hENx hi 129 (by omega), hmh]; simp [mN, hi]
  · rw [hd]; exact (den_indep δF b hn nodes orbit chals pubs col mhv iv av i).trans (by simp [dN])
  · refine (gather_trace b _ e1 CellH.invH (iv i) fun k => ?_).trans ?_
    · rw [hcol0, show 130 + 3 * CellH.invH + (k : ℕ) = 226 + k by simp [CellH.invH], hET _ (by omega),
        hlimbI]
    · simp [iv, ivF, dN]
  · intro hi
    refine (gather_traceNext b _ e1 CellH.invH (iv ⟨(i : ℕ) + 1, hi⟩) fun k => ?_).trans ?_
    · rw [hcolN, show 130 + 3 * CellH.invH + (k : ℕ) = 226 + k by simp [CellH.invH], hENx hi _ (by omega),
        hlimbI]
    · simp [iv, ivF, dN, hi]
  · refine (gather_trace b _ e1 CellH.accH (av i) fun k => ?_).trans ?_
    · rw [hcol0, show 130 + 3 * CellH.accH + (k : ℕ) = 229 + k by simp [CellH.accH], hET _ (by omega),
        hlimbA]
    · rfl
  · intro hi
    refine (gather_traceNext b _ e1 CellH.accH (av ⟨(i : ℕ) + 1, hi⟩) fun k => ?_).trans ?_
    · rw [hcolN, show 130 + 3 * CellH.accH + (k : ℕ) = 229 + k by simp [CellH.accH], hENx hi _ (by omega),
        hlimbA]
    · rfl
  · rw [← hpub]
    simp only [gatherEnv, ChipTemplate.col0, cellTemplateH_baseCols]
    exact sum_slotVal b 130 CellH.pubH pubs

end Main

end CellTraceH

end

end Nock.NockVMROM.Thm54.VclL.Handle
