/-
  Nock/NockVMROM/Thm54/VclL/Handle/WalkTraceH.lean

  Additive.

  The honest 132-column walk columns `col` plus the four handle columns `kL vL kR vR` (`21..24`) and
  the five `𝕂`-roles `hxInv hpInvL hpInvR hxAcc hpAcc` (`37..41`, columns `136..150`).  With the
  inverse fill `den⁻¹`, inclusive prefix sums, booleanity of the kind bits, no vanishing denominator
  and the publics equal to the totals, `walkChipH` accepts it (`expandChip_extend_honest` +
  `walkH_gates_honest`).
-/
import Nock.NockVMROM.Thm54.VclL.Handle.CellTraceH

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

namespace Nock.NockVMROM.Thm54.VclL.Handle

open Nock Nock.Reified Nock.Framework
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Module
open scoped Polynomial

noncomputable section

namespace WalkTraceH

section Data
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
  (δF : F) (kroots : ℕ) (b : Basis (Fin 3) F K) {n : ℕ}

theorem walkTemplate_width : (walkTemplate δF kroots).width 3 = 132 := by
  unfold ChipTemplate.width; rw [walkTemplate_baseCols, walkTemplate_extCols]
theorem walkTemplateH_width : (walkTemplateH δF kroots).width 3 = 151 := by
  unfold ChipTemplate.width; rw [walkTemplateH_baseCols, walkTemplateH_extCols]

/-- The five role fills (limbs). -/
structure Roles (n : ℕ) (K : Type) where
  xi : Fin n → K
  pl : Fin n → K
  pr : Fin n → K
  xa : Fin n → K
  pa : Fin n → K

/-- The new walk-twin columns: `kL vL kR vR` at `21..24`; role limbs at `136..150`. -/
def new (kLv vLv kRv vRv : Fin n → F) (R : Roles n K) : ℕ → Fin n → F := fun j i =>
  if j = 21 then kLv i else if j = 22 then vLv i else if j = 23 then kRv i else if j = 24 then vRv i
  else if 136 ≤ j ∧ j < 139 then coordN b (R.xi i) (j - 136)
  else if 139 ≤ j ∧ j < 142 then coordN b (R.pl i) (j - 139)
  else if 142 ≤ j ∧ j < 145 then coordN b (R.pr i) (j - 142)
  else if 145 ≤ j ∧ j < 148 then coordN b (R.xa i) (j - 145)
  else if 148 ≤ j ∧ j < 151 then coordN b (R.pa i) (j - 148) else 0

def colH (col : ℕ → Fin n → F) (kLv vLv kRv vRv : Fin n → F) (R : Roles n K) : ℕ → Fin n → F :=
  extColF 21 25 ((walkTemplate δF kroots).width 3) col (new b kLv vLv kRv vRv R)

end Data

section Rows
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
  (δF : F) (kroots : ℕ) (b : Basis (Fin 3) F K) {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F)
  (orbit : StrictOrbitDomain F 3 h) (chals pubs : ℕ → K)

def E (col : ℕ → Fin n → F) (kLv vLv kRv vRv : Fin n → F) (R : Roles n K) (i : Fin n) : Env F :=
  Reify.envOfTrace (honestQ hn nodes (colH δF kroots b col kLv vLv kRv vRv R)
    ((walkTemplateH δF kroots).width 3)) orbit.ω (nodes i) (slotVal b 25 chals) (slotVal b 25 pubs)

/-- Denominator of a key list at an environment. -/
def denAt (l : List (CoeffExpr F)) (e : Env F) : K :=
  (CellH.denKey l).eval (gatherEnv b ((walkTemplateH δF kroots).col0 3) e) e

def zeroR : Roles n K := ⟨fun _ => 0, fun _ => 0, fun _ => 0, fun _ => 0, fun _ => 0⟩

/-- Row denominators of the consumed export key and the two provided records (zero role fill; they read
only base columns, `denAt_congr`). -/
def dRow (l : List (CoeffExpr F)) (col : ℕ → Fin n → F) (kLv vLv kRv vRv : Fin n → F) (i : Fin n) : K :=
  denAt δF kroots b l (E δF kroots b hn nodes orbit chals pubs col kLv vLv kRv vRv zeroR i)

end Rows

section Facts
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
  (δF : F) (kroots : ℕ) (b : Basis (Fin 3) F K) {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F)
  (orbit : StrictOrbitDomain F 3 h) (chals pubs : ℕ → K)
  (col : ℕ → Fin n → F) (kLv vLv kRv vRv : Fin n → F)

theorem keys_below (l : List (CoeffExpr F))
    (hl : l = WalkHC.xKeyH ∨ l = WalkHC.recLH ∨ l = WalkHC.recRH) : ∀ g ∈ l, colsBelow 25 g = true := by
  intro g hg
  rcases hl with rfl | rfl | rfl <;>
  · simp only [WalkHC.xKeyH, WalkHC.recLH, WalkHC.recRH, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl <;>
      simp [colsBelow, cv, WChip.idx, WChip.pre, WChip.ridx, WalkHC.kL, WalkHC.vL, WalkHC.kR, WalkHC.vR]

theorem colH_lt25 (R R' : Roles n K) (j : ℕ) (hj : j < 25) :
    colH δF kroots b col kLv vLv kRv vRv R j = colH δF kroots b col kLv vLv kRv vRv R' j := by
  funext i
  by_cases h1 : j < 21
  · simp [colH, extColF, h1]
  · have h2 : 21 ≤ j := by omega
    interval_cases j <;> simp [colH, extColF, new]

end Facts


section RoleLemmas
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
  (δF : F) (kroots : ℕ) (b : Basis (Fin 3) F K) {n : ℕ}
  (col : ℕ → Fin n → F) (kLv vLv kRv vRv : Fin n → F) (R : Roles n K)

theorem colH_role (j : ℕ) (hj : 136 ≤ j) (i : Fin n) :
    colH δF kroots b col kLv vLv kRv vRv R j i = new b kLv vLv kRv vRv R j i := by
  simp only [colH, extColF, walkTemplate_width δF kroots]
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]

theorem new_xi (k : Fin 3) (i : Fin n) : new b kLv vLv kRv vRv R (136 + k) i = coord b (R.xi i) k := by
  have := k.isLt
  simp only [new]
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos ⟨by omega, by omega⟩,
    show 136 + (k : ℕ) - 136 = k by omega]
  exact coordN_eq b _ k
theorem new_pl (k : Fin 3) (i : Fin n) : new b kLv vLv kRv vRv R (139 + k) i = coord b (R.pl i) k := by
  have := k.isLt
  simp only [new]
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_pos ⟨by omega, by omega⟩, show 139 + (k : ℕ) - 139 = k by omega]
  exact coordN_eq b _ k
theorem new_pr (k : Fin 3) (i : Fin n) : new b kLv vLv kRv vRv R (142 + k) i = coord b (R.pr i) k := by
  have := k.isLt
  simp only [new]
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega), if_pos ⟨by omega, by omega⟩, show 142 + (k : ℕ) - 142 = k by omega]
  exact coordN_eq b _ k
theorem new_xa (k : Fin 3) (i : Fin n) : new b kLv vLv kRv vRv R (145 + k) i = coord b (R.xa i) k := by
  have := k.isLt
  simp only [new]
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega), if_neg (by omega), if_pos ⟨by omega, by omega⟩, show 145 + (k : ℕ) - 145 = k by omega]
  exact coordN_eq b _ k
theorem new_pa (k : Fin 3) (i : Fin n) : new b kLv vLv kRv vRv R (148 + k) i = coord b (R.pa i) k := by
  have := k.isLt
  simp only [new]
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos ⟨by omega, by omega⟩,
    show 148 + (k : ℕ) - 148 = k by omega]
  exact coordN_eq b _ k

end RoleLemmas

section Main
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
  (δF : F) (kroots : ℕ) (b : Basis (Fin 3) F K) {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F)
  (orbit : StrictOrbitDomain F 3 h) (chals pubs : ℕ → K)
  (col : ℕ → Fin n → F) (kLv vLv kRv vRv : Fin n → F)

theorem E_below (R R' : Roles n K) (i : Fin n) (j : ℕ) (hj : j < 25) :
    (E δF kroots b hn nodes orbit chals pubs col kLv vLv kRv vRv R i).trace j =
        (E δF kroots b hn nodes orbit chals pubs col kLv vLv kRv vRv R' i).trace j ∧
    (E δF kroots b hn nodes orbit chals pubs col kLv vLv kRv vRv R i).traceNext j =
        (E δF kroots b hn nodes orbit chals pubs col kLv vLv kRv vRv R' i).traceNext j := by
  have hw : j < (walkTemplateH δF kroots).width 3 := by rw [walkTemplateH_width]; omega
  have hq := honestQ_congr hn nodes (colH δF kroots b col kLv vLv kRv vRv R)
    (colH δF kroots b col kLv vLv kRv vRv R') ((walkTemplateH δF kroots).width 3) ⟨j, hw⟩
    (colH_lt25 δF kroots b col kLv vLv kRv vRv R R' j hj)
  simp [E, Reify.envOfTrace, dif_pos hw, hq]

theorem gather_chal (e : Env F) (hc : e.chal = slotVal b 25 chals) (r : ℕ) :
    (gatherEnv b ((walkTemplateH δF kroots).col0 3) e).chal r = chals r := by
  simp only [gatherEnv, ChipTemplate.col0, hc, walkTemplateH_baseCols]
  exact sum_slotVal b 25 r chals

theorem denAt_congr (l : List (CoeffExpr F)) (hl : ∀ g ∈ l, colsBelow 25 g = true) (e e' : Env F)
    (hc : e.chal = slotVal b 25 chals) (hc' : e'.chal = slotVal b 25 chals)
    (ht : ∀ j < 25, e.trace j = e'.trace j) (hn : ∀ j < 25, e.traceNext j = e'.traceNext j) :
    denAt δF kroots b l e = denAt δF kroots b l e' := by
  unfold denAt
  rw [denKey_eval, denKey_eval, gather_chal δF kroots b chals e hc, gather_chal δF kroots b chals e hc,
    gather_chal δF kroots b chals e' hc', gather_chal δF kroots b chals e' hc']
  have hm : (l.zipIdx 0).map
        (fun p : CoeffExpr F × ℕ => chals CellH.hGam ^ p.2 * algebraMap F K (p.1.eval e)) =
      (l.zipIdx 0).map
        (fun p : CoeffExpr F × ℕ => chals CellH.hGam ^ p.2 * algebraMap F K (p.1.eval e')) := by
    refine List.map_congr_left fun p hp => ?_
    rw [colsBelow_eval (hl p.1 (List.fst_mem_of_mem_zipIdx hp)) ht hn]
  rw [hm]

theorem den_indep (l : List (CoeffExpr F)) (hl : ∀ g ∈ l, colsBelow 25 g = true) (R : Roles n K)
    (i : Fin n) :
    denAt δF kroots b l (E δF kroots b hn nodes orbit chals pubs col kLv vLv kRv vRv R i) =
      dRow δF kroots b hn nodes orbit chals pubs l col kLv vLv kRv vRv i :=
  denAt_congr δF kroots b chals l hl _ _ rfl rfl
    (fun j hj => (E_below δF kroots b hn nodes orbit chals pubs col kLv vLv kRv vRv R zeroR i j hj).1)
    (fun j hj => (E_below δF kroots b hn nodes orbit chals pubs col kLv vLv kRv vRv R zeroR i j hj).2)

end Main

section Accept
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
  (δF : F) (kroots : ℕ) (b : Basis (Fin 3) F K) {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F)
  (orbit : StrictOrbitDomain F 3 h) (chals pubs : ℕ → K)
  (col : ℕ → Fin n → F) (kLv vLv kRv vRv : Fin n → F)

/-- ℕ-indexed data (padding off the table). -/
def cN (j : ℕ) (c : Fin n → F) : F := if hj : j < n then c ⟨j, hj⟩ else 0
def dN (l : List (CoeffExpr F)) (j : ℕ) : K :=
  if hj : j < n then dRow δF kroots b hn nodes orbit chals pubs l col kLv vLv kRv vRv ⟨j, hj⟩ else 1

/-- **The honest role fill**: inverses `den⁻¹`, inclusive prefix sums. -/
def rolesF : Roles n K where
  xi := fun i => (dRow δF kroots b hn nodes orbit chals pubs WalkHC.xKeyH col kLv vLv kRv vRv i)⁻¹
  pl := fun i => (dRow δF kroots b hn nodes orbit chals pubs WalkHC.recLH col kLv vLv kRv vRv i)⁻¹
  pr := fun i => (dRow δF kroots b hn nodes orbit chals pubs WalkHC.recRH col kLv vLv kRv vRv i)⁻¹
  xa := fun i => ∑ j ∈ Finset.range (i + 1),
    (dN δF kroots b hn nodes orbit chals pubs col kLv vLv kRv vRv WalkHC.xKeyH j)⁻¹
  pa := fun i => ∑ j ∈ Finset.range (i + 1),
    (algebraMap F K (cN j (col WChip.mL)) *
        (dN δF kroots b hn nodes orbit chals pubs col kLv vLv kRv vRv WalkHC.recLH j)⁻¹ +
      algebraMap F K (cN j (col WChip.mR)) *
        (dN δF kroots b hn nodes orbit chals pubs col kLv vLv kRv vRv WalkHC.recRH j)⁻¹)

/-- **`walkTraceH`**: the honest 151-column walk twin trace. -/
def walkTraceH :=
  honestQ hn nodes (colH δF kroots b col kLv vLv kRv vRv
    (rolesF δF kroots b hn nodes orbit chals pubs col kLv vLv kRv vRv)) ((walkTemplateH δF kroots).width 3)

/-- **The walk twin accepts `walkTraceH`.**  From the original honest walk acceptance `hsat0`, boolean
kind bits, no vanishing denominator (the priced pole event) and the publics equal to the totals. -/
theorem walkChipH_accepts_honest (hinj : Function.Injective nodes)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω)
    (hsat0 : (walkChip δF kroots b hn nodes orbit chals pubs).rap.Satisfies (honestQ hn nodes col _))
    (hkL : ∀ i, kLv i = 0 ∨ kLv i = 1) (hkR : ∀ i, kRv i = 0 ∨ kRv i = 1)
    (hpX : ∀ i, dRow δF kroots b hn nodes orbit chals pubs WalkHC.xKeyH col kLv vLv kRv vRv i ≠ 0)
    (hpL : ∀ i, dRow δF kroots b hn nodes orbit chals pubs WalkHC.recLH col kLv vLv kRv vRv i ≠ 0)
    (hpR : ∀ i, dRow δF kroots b hn nodes orbit chals pubs WalkHC.recRH col kLv vLv kRv vRv i ≠ 0)
    (hpubX : pubs WalkHC.pubX = ∑ j ∈ Finset.range n,
      (dN δF kroots b hn nodes orbit chals pubs col kLv vLv kRv vRv WalkHC.xKeyH j)⁻¹)
    (hpubP : pubs WalkHC.pubP = ∑ j ∈ Finset.range n,
      (algebraMap F K (cN j (col WChip.mL)) *
          (dN δF kroots b hn nodes orbit chals pubs col kLv vLv kRv vRv WalkHC.recLH j)⁻¹ +
        algebraMap F K (cN j (col WChip.mR)) *
          (dN δF kroots b hn nodes orbit chals pubs col kLv vLv kRv vRv WalkHC.recRH j)⁻¹)) :
    (walkChipH δF kroots b hn nodes orbit chals pubs).rap.Satisfies
      (walkTraceH δF kroots b hn nodes orbit chals pubs col kLv vLv kRv vRv) := by
  have hW : (walkTemplate δF kroots).width 3 = 132 := walkTemplate_width δF kroots
  have hW' : (walkTemplateH δF kroots).width 3 = 151 := walkTemplateH_width δF kroots
  set R := rolesF δF kroots b hn nodes orbit chals pubs col kLv vLv kRv vRv with hR
  refine expandChip_extend_honest b orbit (rowNodeSet nodes) chals pubs (walkTemplate δF kroots)
    (walkTemplateH δF kroots) 21 25 (walkTemplate_baseCols δF kroots) (walkTemplateH_baseCols δF kroots)
    (by omega) (by omega) (by rw [walkTemplate_extCols, walkTemplateH_extCols]; omega)
    (fun g hg => ⟨List.mem_append_left _ hg, walkBase_below kroots g hg⟩)
    (fun g hg => ⟨List.mem_append_left _ hg, by rw [walkTemplate_extCols]; exact walkMixed_below δF kroots g hg⟩)
    rfl rfl hn nodes col (new b kLv vLv kRv vRv R) hsat0 ?_ ?_
  all_goals
    intro x hx g hg hg0
    obtain ⟨i, rfl⟩ := (mem_rowNodeSet_iff nodes x).mp hx
    have hE : Reify.envOfTrace (honestQ hn nodes (extColF 21 25 ((walkTemplate δF kroots).width 3) col
        (new b kLv vLv kRv vRv R)) ((walkTemplateH δF kroots).width 3)) orbit.ω (nodes i)
        (slotVal b 25 chals) (slotVal b 25 pubs) =
        E δF kroots b hn nodes orbit chals pubs col kLv vLv kRv vRv R i := rfl
    rw [hE]
    set e1 := E δF kroots b hn nodes orbit chals pubs col kLv vLv kRv vRv R i with he1
    have hwlt : ∀ j, j < 151 → j < (walkTemplateH δF kroots).width 3 := fun j hj => by omega
    have hET : ∀ j, j < 151 → e1.trace j = fullCol hn (colH δF kroots b col kLv vLv kRv vRv R) j i :=
      fun j hj => env_trace hn nodes hinj _ _ _ _ i (hwlt j hj)
    have hENx : ∀ (hi : (i : ℕ) + 1 < n) j, j < 151 →
        e1.traceNext j = fullCol hn (colH δF kroots b col kLv vLv kRv vRv R) j ⟨(i : ℕ) + 1, hi⟩ :=
      fun hi j hj => env_traceNext hn nodes hinj _ _ _ _ hadj i hi (hwlt j hj)
    have hnew : ∀ j, 2 ≤ j → fullCol hn (colH δF kroots b col kLv vLv kRv vRv R) j =
        colH δF kroots b col kLv vLv kRv vRv R j := by
      intro j hj; funext i'; simp only [fullCol]; split_ifs <;> first | omega | rfl
    have hkLc : ∀ i' : Fin n, fullCol hn (colH δF kroots b col kLv vLv kRv vRv R) 21 i' = kLv i' := by
      intro i'; rw [hnew _ (by omega)]; simp [colH, extColF, new]
    have hvLc : ∀ i' : Fin n, fullCol hn (colH δF kroots b col kLv vLv kRv vRv R) 22 i' = vLv i' := by
      intro i'; rw [hnew _ (by omega)]; simp [colH, extColF, new]
    have hkRc : ∀ i' : Fin n, fullCol hn (colH δF kroots b col kLv vLv kRv vRv R) 23 i' = kRv i' := by
      intro i'; rw [hnew _ (by omega)]; simp [colH, extColF, new]
    have hvRc : ∀ i' : Fin n, fullCol hn (colH δF kroots b col kLv vLv kRv vRv R) 24 i' = vRv i' := by
      intro i'; rw [hnew _ (by omega)]; simp [colH, extColF, new]
    have hbelow : ∀ j, 2 ≤ j → j < 21 → fullCol hn (colH δF kroots b col kLv vLv kRv vRv R) j i = col j i := by
      intro j h2 h21; rw [hnew _ h2]; simp [colH, extColF, h21]
    have hbelow' : ∀ (hi : (i : ℕ) + 1 < n) (j : ℕ), 2 ≤ j → j < 21 →
        fullCol hn (colH δF kroots b col kLv vLv kRv vRv R) j ⟨(i : ℕ) + 1, hi⟩ = col j ⟨(i : ℕ) + 1, hi⟩ := by
      intro hi j h2 h21; rw [hnew _ h2]; simp [colH, extColF, h21]
    have hcol0 : ∀ r k : ℕ, (walkTemplateH δF kroots).col0 3 .traceCur r + k = 25 + 3 * r + k := by
      intro r k; simp only [ChipTemplate.col0, walkTemplateH_baseCols]
    have hcolN : ∀ r k : ℕ, (walkTemplateH δF kroots).col0 3 .traceNext r + k = 25 + 3 * r + k := hcol0
    have hlimbXi : ∀ (i' : Fin n) (k : Fin 3), fullCol hn (colH δF kroots b col kLv vLv kRv vRv R) (136 + k) i' =
        coord b (R.xi i') k := by
      intro i' k; have hk := k.isLt
      rw [hnew _ (by omega), colH_role δF kroots b col kLv vLv kRv vRv R _ (by omega)]
      exact new_xi b kLv vLv kRv vRv R k i'
    have hlimbPl : ∀ (i' : Fin n) (k : Fin 3), fullCol hn (colH δF kroots b col kLv vLv kRv vRv R) (139 + k) i' =
        coord b (R.pl i') k := by
      intro i' k; have hk := k.isLt
      rw [hnew _ (by omega), colH_role δF kroots b col kLv vLv kRv vRv R _ (by omega)]
      exact new_pl b kLv vLv kRv vRv R k i'
    have hlimbPr : ∀ (i' : Fin n) (k : Fin 3), fullCol hn (colH δF kroots b col kLv vLv kRv vRv R) (142 + k) i' =
        coord b (R.pr i') k := by
      intro i' k; have hk := k.isLt
      rw [hnew _ (by omega), colH_role δF kroots b col kLv vLv kRv vRv R _ (by omega)]
      exact new_pr b kLv vLv kRv vRv R k i'
    have hlimbXa : ∀ (i' : Fin n) (k : Fin 3), fullCol hn (colH δF kroots b col kLv vLv kRv vRv R) (145 + k) i' =
        coord b (R.xa i') k := by
      intro i' k; have hk := k.isLt
      rw [hnew _ (by omega), colH_role δF kroots b col kLv vLv kRv vRv R _ (by omega)]
      exact new_xa b kLv vLv kRv vRv R k i'
    have hlimbPa : ∀ (i' : Fin n) (k : Fin 3), fullCol hn (colH δF kroots b col kLv vLv kRv vRv R) (148 + k) i' =
        coord b (R.pa i') k := by
      intro i' k; have hk := k.isLt
      rw [hnew _ (by omega), colH_role δF kroots b col kLv vLv kRv vRv R _ (by omega)]
      exact new_pa b kLv vLv kRv vRv R k i'
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
       have hgm : g ∈ WalkHC.gates (F := F) := by
         have hg' : g ∈ WChip.mixedGates δF kroots ++ WalkHC.gates (F := F) := hg
         rcases List.mem_append.mp hg' with h1 | h1
         · exact absurd h1 hg0
         · exact h1
       have hd : ∀ (l : List (CoeffExpr F)) (i' : Fin n),
           dN δF kroots b hn nodes orbit chals pubs col kLv vLv kRv vRv l i' =
             dRow δF kroots b hn nodes orbit chals pubs l col kLv vLv kRv vRv i' := fun l i' => by simp [dN]
       have hmLc : e1.trace WChip.mL = cN i (col WChip.mL) := by
         show e1.trace 10 = _; rw [hET 10 (by omega), hbelow 10 (by omega) (by omega)]; simp [cN, WChip.mL]
       have hmRc : e1.trace WChip.mR = cN i (col WChip.mR) := by
         show e1.trace 11 = _; rw [hET 11 (by omega), hbelow 11 (by omega) (by omega)]; simp [cN, WChip.mR]
       have hmLn : ∀ hi : (i : ℕ) + 1 < n, e1.traceNext WChip.mL = cN ((i : ℕ) + 1) (col WChip.mL) := by
         intro hi; show e1.traceNext 10 = _
         rw [hENx hi 10 (by omega), hbelow' hi 10 (by omega) (by omega)]; simp [cN, hi, WChip.mL]
       have hmRn : ∀ hi : (i : ℕ) + 1 < n, e1.traceNext WChip.mR = cN ((i : ℕ) + 1) (col WChip.mR) := by
         intro hi; show e1.traceNext 11 = _
         rw [hENx hi 11 (by omega), hbelow' hi 11 (by omega) (by omega)]; simp [cN, hi, WChip.mR]
       refine walkH_gates_honest (gatherEnv b ((walkTemplateH δF kroots).col0 3) e1) e1 n i i.isLt
         (fun j => cN j (col WChip.mL)) (fun j => cN j (col WChip.mR))
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
           (keys_below _ (Or.inl rfl)) R i).trans (hd _ i).symm
       · exact (den_indep δF kroots b hn nodes orbit chals pubs col kLv vLv kRv vRv _
           (keys_below _ (Or.inr (Or.inl rfl))) R i).trans (hd _ i).symm
       · exact (den_indep δF kroots b hn nodes orbit chals pubs col kLv vLv kRv vRv _
           (keys_below _ (Or.inr (Or.inr rfl))) R i).trans (hd _ i).symm
       · refine (gather_trace b _ e1 WalkHC.hxInv (R.xi i) fun k => ?_).trans ?_
         · rw [hcol0, show 25 + 3 * WalkHC.hxInv + (k : ℕ) = 136 + k by simp [WalkHC.hxInv], hET _ (by omega), hlimbXi]
         · simp [R, rolesF, dN]
       · intro hi
         refine (gather_traceNext b _ e1 WalkHC.hxInv (R.xi ⟨(i : ℕ) + 1, hi⟩) fun k => ?_).trans ?_
         · rw [hcolN, show 25 + 3 * WalkHC.hxInv + (k : ℕ) = 136 + k by simp [WalkHC.hxInv], hENx hi _ (by omega), hlimbXi]
         · simp [R, rolesF, dN, hi]
       · refine (gather_trace b _ e1 WalkHC.hpInvL (R.pl i) fun k => ?_).trans ?_
         · rw [hcol0, show 25 + 3 * WalkHC.hpInvL + (k : ℕ) = 139 + k by simp [WalkHC.hpInvL], hET _ (by omega), hlimbPl]
         · simp [R, rolesF, dN]
       · refine (gather_trace b _ e1 WalkHC.hpInvR (R.pr i) fun k => ?_).trans ?_
         · rw [hcol0, show 25 + 3 * WalkHC.hpInvR + (k : ℕ) = 142 + k by simp [WalkHC.hpInvR], hET _ (by omega), hlimbPr]
         · simp [R, rolesF, dN]
       · intro hi
         refine (gather_traceNext b _ e1 WalkHC.hpInvL (R.pl ⟨(i : ℕ) + 1, hi⟩) fun k => ?_).trans ?_
         · rw [hcolN, show 25 + 3 * WalkHC.hpInvL + (k : ℕ) = 139 + k by simp [WalkHC.hpInvL], hENx hi _ (by omega), hlimbPl]
         · simp [R, rolesF, dN, hi]
       · intro hi
         refine (gather_traceNext b _ e1 WalkHC.hpInvR (R.pr ⟨(i : ℕ) + 1, hi⟩) fun k => ?_).trans ?_
         · rw [hcolN, show 25 + 3 * WalkHC.hpInvR + (k : ℕ) = 142 + k by simp [WalkHC.hpInvR], hENx hi _ (by omega), hlimbPr]
         · simp [R, rolesF, dN, hi]
       · refine (gather_trace b _ e1 WalkHC.hxAcc (R.xa i) fun k => ?_).trans ?_
         · rw [hcol0, show 25 + 3 * WalkHC.hxAcc + (k : ℕ) = 145 + k by simp [WalkHC.hxAcc], hET _ (by omega), hlimbXa]
         · rfl
       · intro hi
         refine (gather_traceNext b _ e1 WalkHC.hxAcc (R.xa ⟨(i : ℕ) + 1, hi⟩) fun k => ?_).trans ?_
         · rw [hcolN, show 25 + 3 * WalkHC.hxAcc + (k : ℕ) = 145 + k by simp [WalkHC.hxAcc], hENx hi _ (by omega), hlimbXa]
         · rfl
       · refine (gather_trace b _ e1 WalkHC.hpAcc (R.pa i) fun k => ?_).trans ?_
         · rw [hcol0, show 25 + 3 * WalkHC.hpAcc + (k : ℕ) = 148 + k by simp [WalkHC.hpAcc], hET _ (by omega), hlimbPa]
         · rfl
       · intro hi
         refine (gather_traceNext b _ e1 WalkHC.hpAcc (R.pa ⟨(i : ℕ) + 1, hi⟩) fun k => ?_).trans ?_
         · rw [hcolN, show 25 + 3 * WalkHC.hpAcc + (k : ℕ) = 148 + k by simp [WalkHC.hpAcc], hENx hi _ (by omega), hlimbPa]
         · rfl
       · rw [← hpubX]
         simp only [gatherEnv, ChipTemplate.col0, walkTemplateH_baseCols]
         exact sum_slotVal b 25 WalkHC.pubX pubs
       · rw [← hpubP]
         simp only [gatherEnv, ChipTemplate.col0, walkTemplateH_baseCols]
         exact sum_slotVal b 25 WalkHC.pubP pubs)

end Accept

end WalkTraceH

end

end Nock.NockVMROM.Thm54.VclL.Handle
