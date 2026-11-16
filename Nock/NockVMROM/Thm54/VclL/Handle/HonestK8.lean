/-
  Nock/NockVMROM/Thm54/VclL/Handle/HonestK8.lean

* `cellChipHQK_accepts_honest`: `cellChipHQK` accepts the honest extension of an accepted
    `cellChipHQ` trace by the kind columns `kb` (130, 131) and `inv = (lo+hi)⁻¹` (132, 133), under the
    per-row side condition (`kb = 0` and a nonzero-rank weighted child, or `kb = 1` and a rank-(0,0)
    weighted child: a big-atom child).
-/
import Nock.NockVMROM.Thm54.VclL.Handle.CellTwinK
import Nock.NockVMROM.Thm54.VclL.Handle.CellTraceHQ
import Nock.NockVMROM.Thm54.VclL.Handle.HonestTwinQ
import Nock.NockVMROM.Thm54.VclL.Handle.WalkJ8

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace Nock.NockVMROM.Thm54.VclL.Handle.HonestK8

open Nock Nock.Reified Nock.Framework
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.VclL.Handle Nock.NockVMROM.Thm54.VclL.Handle.CellTwinK Nock.NockVMROM.Thm54.VclL.Handle.RangeHQ
open Module
open scoped Polynomial

noncomputable section

/-! ## 1. The side gates at an honest row (both kinds) -/

section Side
variable {F : Type} [Field F]

/-- The honest side data of one child: a small atom or a cell child (`kb = 0`, weight `0` or `1`
with nonzero rank) or a big-atom child (`kb = 1`, weight `1`, rank `(0,0)`). -/
def SideOK (kb w lo hi : F) : Prop :=
  (kb = 0 ∧ (w = 0 ∨ (w = 1 ∧ lo + hi ≠ 0))) ∨ (kb = 1 ∧ w = 1 ∧ lo = 0 ∧ hi = 0)

theorem sideGates_honest2 (kb inv w lo hi : ℕ) (e : Env F)
    (hinv : e.trace inv = (e.trace lo + e.trace hi)⁻¹)
    (hs : SideOK (e.trace kb) (e.trace w) (e.trace lo) (e.trace hi)) :
    ∀ g ∈ (sideGates (F := F) kb inv w lo hi), g.eval e = 0 := by
  rcases hs with ⟨hkb, hw⟩ | ⟨hkb, hw, hl, hh⟩
  · exact sideGates_honest kb inv w lo hi e hkb hinv hw
  · intro g hg
    simp only [sideGates, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl <;> simp [CoeffExpr.eval, notE, boolE, hkb, hw, hl, hh]

end Side

/-! ## 2. The cell twin -/

section Cell
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
  (δF : F) (b : Basis (Fin 3) F K) {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F)
  (orbit : StrictOrbitDomain F 3 h) (chals pubs : ℕ → K)
  (col : ℕ → Fin n → F) (kbLv kbRv : Fin n → F)

/-- The new columns: `kb` at `130, 131`, `inv = (lo+hi)⁻¹` at `132, 133`. -/
def newK : ℕ → Fin n → F := fun j i =>
  if j = kbL then kbLv i else if j = kbR then kbRv i
  else if j = invL then (col Cell.loL i + col Cell.hiL i)⁻¹
  else (col Cell.loR i + col Cell.hiR i)⁻¹

/-- **The honest `cellChipHQK` trace**. -/
def cellTraceHQK :=
  honestQ hn nodes (extColF 130 134 ((cellTemplateHQ δF).width 3) col (newK col kbLv kbRv)) 242

theorem cellChipHQK_accepts_honest (hinj : Function.Injective nodes)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω)
    (hsat0 : (cellChipHQ δF b hn nodes orbit chals pubs).rap.Satisfies (honestQ hn nodes col _))
    (hL : ∀ i, SideOK (kbLv i) (col Cell.wL i) (col Cell.loL i) (col Cell.hiL i))
    (hR : ∀ i, SideOK (kbRv i) (col Cell.wR i) (col Cell.loR i) (col Cell.hiR i)) :
    (cellChipHQK δF b hn nodes orbit chals pubs).rap.Satisfies
      (cellTraceHQK δF hn nodes col kbLv kbRv) := by
  have hW' : (cellTemplateHQ δF).width 3 = 238 := CellTraceHQ.cellTemplateHQ_width δF
  have hWK : (cellTemplateHQK δF).width 3 = 242 := by
    unfold ChipTemplate.width; rw [cellTemplateHQK_baseCols, cellTemplateHQK_extCols]
  obtain ⟨hB, hM, -, -⟩ := cellHQ_range δF
  have := expandChip_extend_honest b orbit (rowNodeSet nodes) chals pubs (cellTemplateHQ δF)
    (cellTemplateHQK δF) 130 134 (cellTemplateHQ_baseCols δF) (cellTemplateHQK_baseCols δF)
    (by omega) (by omega) (by simp only [cellTemplateHQ_extCols, cellTemplateHQK_extCols]; omega)
    (fun g hg => ⟨List.mem_append_left _ hg, by
      have := hB g hg; rwa [cellTemplateHQ_baseCols] at this⟩)
    (fun g hg => ⟨hg, by
      have := hM g hg; rwa [cellTemplateHQ_baseCols, cellTemplateHQ_extCols] at this⟩)
    rfl rfl hn nodes col (newK col kbLv kbRv) hsat0 ?_ ?_
  · rw [hW'] at this
    exact this
  · intro x hx g hg hg0
    obtain ⟨i, rfl⟩ := (mem_rowNodeSet_iff nodes x).mp hx
    have hgk : g ∈ kindGates (F := F) := by
      have hg' : g ∈ Cell.baseGates ++ kindGates (F := F) := hg
      rcases List.mem_append.mp hg' with h1 | h1
      · exact absurd h1 hg0
      · exact h1
    set e1 := Reify.envOfTrace (honestQ hn nodes (extColF 130 134 ((cellTemplateHQ δF).width 3) col
      (newK col kbLv kbRv)) ((cellTemplateHQK δF).width 3)) orbit.ω (nodes i) (slotVal b 134 chals)
      (slotVal b 134 pubs) with he1
    have hET : ∀ j, j < 242 → e1.trace j = fullCol hn (extColF 130 134 ((cellTemplateHQ δF).width 3) col
        (newK col kbLv kbRv)) j i := fun j hj => env_trace hn nodes hinj _ _ _ _ i (by omega)
    have hlow : ∀ j, 2 ≤ j → j < 130 → e1.trace j = col j i := by
      intro j h2 h130
      rw [hET j (by omega)]
      simp only [fullCol, extColF]
      rw [if_neg (by omega), if_neg (by omega), if_pos h130]
    have hnew : ∀ j, 130 ≤ j → j < 134 → e1.trace j = newK col kbLv kbRv j i := by
      intro j h1 h2
      rw [hET j (by omega)]
      have h3 : ¬ j < 130 := by omega
      simp [fullCol, extColF, h3, h2, show j ≠ 0 by omega, show j ≠ 1 by omega]
    have cL : ∀ j, j ∈ [Cell.wL, Cell.loL, Cell.hiL, Cell.wR, Cell.loR, Cell.hiR] → e1.trace j = col j i := by
      intro j hj
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
      apply hlow j <;> rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [Cell.wL, Cell.loL, Cell.hiL, Cell.wR, Cell.loR, Cell.hiR]
    have kL : e1.trace kbL = kbLv i := by
      rw [hnew kbL (by simp [kbL]) (by simp [kbL])]; simp [newK]
    have kR : e1.trace kbR = kbRv i := by
      rw [hnew kbR (by simp [kbR]) (by simp [kbR])]; simp [newK, kbL, kbR]
    have iL : e1.trace invL = (e1.trace Cell.loL + e1.trace Cell.hiL)⁻¹ := by
      rw [hnew invL (by simp [invL]) (by simp [invL]), cL Cell.loL (by simp), cL Cell.hiL (by simp)]
      simp [newK, kbL, kbR, invL]
    have iR : e1.trace invR = (e1.trace Cell.loR + e1.trace Cell.hiR)⁻¹ := by
      rw [hnew invR (by simp [invR]) (by simp [invR]), cL Cell.loR (by simp), cL Cell.hiR (by simp)]
      simp [newK, kbL, kbR, invL, invR]
    have sL := sideGates_honest2 kbL invL Cell.wL Cell.loL Cell.hiL e1 iL (by
      rw [kL, cL Cell.wL (by simp), cL Cell.loL (by simp), cL Cell.hiL (by simp)]; exact hL i)
    have sR := sideGates_honest2 kbR invR Cell.wR Cell.loR Cell.hiR e1 iR (by
      rw [kR, cL Cell.wR (by simp), cL Cell.loR (by simp), cL Cell.hiR (by simp)]; exact hR i)
    simp only [kindGates, List.mem_append] at hgk
    rcases hgk with h1 | h1
    · exact sL g h1
    · exact sR g h1
  · intro x hx g hg hg0
    exact absurd hg hg0

/-- **With the fixed preprocessing** (masks `0`, `1`). -/
theorem cellChipHQK_accepts_honest_pp (hinj : Function.Injective nodes)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω)
    (hsat0 : (cellChipHQ δF b hn nodes orbit chals pubs).rap.Satisfies (honestQ hn nodes col _))
    (hL : ∀ i, SideOK (kbLv i) (col Cell.wL i) (col Cell.loL i) (col Cell.hiL i))
    (hR : ∀ i, SideOK (kbRv i) (col Cell.wR i) (col Cell.loR i) (col Cell.hiR i)) :
    RAP.SatisfiesWithPreprocessing (cellChipHQK δF b hn nodes orbit chals pubs)
      (fun j => cellTraceHQK δF hn nodes col kbLv kbRv
        (Fin.cast (cellChipHQK_width δF b hn nodes orbit chals pubs) j)) := by
  refine ⟨?_, ?_⟩
  · exact cellChipHQK_accepts_honest δF b hn nodes orbit chals pubs col kbLv kbRv hinj hadj hsat0 hL hR
  · intro j
    fin_cases j
    · exact honestQ_zero hn nodes _ (by omega)
    · exact honestQ_one hn nodes _ (by omega)

/-- **The pipeline from the 40th's honest cell acceptance**: the `ok`-gated original acceptance, no
vanishing `𝕂′` denominator, the `𝕂′` public equal to the total, and the side data of the kind bits
⇒ `cellChipHQK` accepts the honest `cellTraceHQ` extended by `kb`, `inv`. -/
theorem cellTwinK_accepted [Fintype K] [Fact (¬ IsSquare (algebraMap F K δF))]
    (mhv : Fin n → F) (hinj : Function.Injective nodes)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω)
    (hok : RAP.SatisfiesWithPreprocessing (cellChipOk δF b hn nodes orbit chals pubs true)
      (fun j => honestQ hn nodes col 225
        (Fin.cast (cellChipOk_w δF b hn nodes orbit chals pubs true) j)))
    (hpole : ∀ i, CellTraceHQ.dRow δF b hn nodes orbit chals pubs col mhv i ≠ 0)
    (hpub : Quad.mk _ (pubs CellHQ.pubHQ) (pubs (CellHQ.pubHQ + 1)) = ∑ j ∈ Finset.range n,
      liftQ δF (CellTraceH.mN mhv j) * (CellTraceHQ.dN δF b hn nodes orbit chals pubs col mhv j)⁻¹)
    (hL : ∀ i, SideOK (kbLv i) (col Cell.wL i) (col Cell.loL i) (col Cell.hiL i))
    (hR : ∀ i, SideOK (kbRv i) (col Cell.wR i) (col Cell.loR i) (col Cell.hiR i)) :
    RAP.SatisfiesWithPreprocessing (cellChipHQK δF b hn nodes orbit chals pubs)
      (fun j => cellTraceHQK δF hn nodes
        (CellTraceHQ.colHQ δF b col mhv (CellTraceHQ.ivF δF b hn nodes orbit chals pubs col mhv)
          (CellTraceHQ.avF δF b hn nodes orbit chals pubs col mhv)) kbLv kbRv
        (Fin.cast (cellChipHQK_width δF b hn nodes orbit chals pubs) j)) := by
  have hq := (cellTwinQ_accepted δF b hn nodes orbit chals pubs col mhv hinj hadj hok hpole hpub).1
  have lo : ∀ j, j < 129 → CellTraceHQ.colHQ δF b col mhv (CellTraceHQ.ivF δF b hn nodes orbit chals pubs col mhv)
      (CellTraceHQ.avF δF b hn nodes orbit chals pubs col mhv) j = col j := by
    intro j hj; funext i; simp [CellTraceHQ.colHQ, extColF, CellTraceHQ.new, hj]
  refine cellChipHQK_accepts_honest_pp δF b hn nodes orbit chals pubs _ kbLv kbRv hinj hadj hq ?_ ?_
  · intro i
    simpa only [lo Cell.wL (by simp [Cell.wL]), lo Cell.loL (by simp [Cell.loL]), lo Cell.hiL (by simp [Cell.hiL])]
      using hL i
  · intro i
    simpa only [lo Cell.wR (by simp [Cell.wR]), lo Cell.loR (by simp [Cell.loR]), lo Cell.hiR (by simp [Cell.hiR])]
      using hR i

/-- The `kb ≡ 0` case: no big-atom child. -/
theorem sideOK_zero {w lo hi : F} (h : w = 0 ∨ (w = 1 ∧ lo + hi ≠ 0)) : SideOK (0 : F) w lo hi :=
  Or.inl ⟨rfl, h⟩

end Cell

end

end Nock.NockVMROM.Thm54.VclL.Handle.HonestK8

/-! ## 3. The ternary walk twin (kinds `0, 1, 2`): `walkChipHQ_accepts_honest` with the base gates `baseHK`.
LABEL: the proof is the 40th's `WalkTraceHQ.walkChipHQ_accepts_honest` with exactly the base-gate case
changed (`ternE` for `boolE`); every other step is the same text over `walkTemplateHQK`
(`walkHQK_unchanged`: only `baseH` differs). -/

namespace Nock.NockVMROM.Thm54.VclL.Handle.WalkTraceHQ

open Nock Nock.Reified Nock.Framework
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.VclL.Handle Nock.NockVMROM.Thm54.VclL.Handle.CellTwinK
open Module
open scoped Polynomial

noncomputable section

section MainK
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [Fintype K]
  (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))] (kroots : ℕ) (b : Basis (Fin 3) F K) {h n : ℕ}
  (hn : 0 < n) (nodes : Fin n → F) (orbit : StrictOrbitDomain F 3 h) (chals pubs : ℕ → K)
  (col : ℕ → Fin n → F) (kLv vLv kRv vRv : Fin n → F)

theorem walkChipHQK_accepts_honest (hinj : Function.Injective nodes)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω)
    (hsat0 : (walkChip δF kroots b hn nodes orbit chals pubs).rap.Satisfies (honestQ hn nodes col _))
    (hkL : ∀ i, kLv i = 0 ∨ kLv i = 1 ∨ kLv i = 2) (hkR : ∀ i, kRv i = 0 ∨ kRv i = 1 ∨ kRv i = 2)
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
    (walkChipHQK δF kroots b hn nodes orbit chals pubs).rap.Satisfies
      (walkTraceHQ δF kroots b hn nodes orbit chals pubs col kLv vLv kRv vRv) := by
  have hW : (walkTemplate δF kroots).width 3 = 132 := WalkTraceH.walkTemplate_width δF kroots
  have hW' : (walkTemplateHQK δF kroots).width 3 = 166 := walkTemplateHQK_width δF kroots
  set R := rolesF δF kroots b hn nodes orbit chals pubs col kLv vLv kRv vRv with hR
  refine expandChip_extend_honest b orbit (rowNodeSet nodes) chals pubs (walkTemplate δF kroots)
    (walkTemplateHQK δF kroots) 21 25 (walkTemplate_baseCols δF kroots) (walkTemplateHQK_baseCols δF kroots)
    (by omega) (by omega) (by rw [walkTemplate_extCols, walkTemplateHQK_extCols]; omega)
    (fun g hg => ⟨List.mem_append_left _ hg, walkBase_below kroots g hg⟩)
    (fun g hg => ⟨List.mem_append_left _ hg, by rw [walkTemplate_extCols]; exact walkMixed_below δF kroots g hg⟩)
    rfl rfl hn nodes col (new δF b kLv vLv kRv vRv R) hsat0 ?_ ?_
  all_goals
    intro x hx g hg hg0
    obtain ⟨i, rfl⟩ := (mem_rowNodeSet_iff nodes x).mp hx
    have hE : Reify.envOfTrace (honestQ hn nodes (extColF 21 25 ((walkTemplate δF kroots).width 3) col
        (new δF b kLv vLv kRv vRv R)) ((walkTemplateHQK δF kroots).width 3)) orbit.ω (nodes i)
        (slotVal b 25 chals) (slotVal b 25 pubs) =
        E δF kroots b hn nodes orbit chals pubs col kLv vLv kRv vRv R i := rfl
    rw [hE]
    set e1 := E δF kroots b hn nodes orbit chals pubs col kLv vLv kRv vRv R i with he1
    have hwlt : ∀ j, j < 166 → j < (walkTemplateHQK δF kroots).width 3 := fun j hj => by omega
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
    have hcol0 : ∀ r k : ℕ, (walkTemplateHQK δF kroots).col0 3 .traceCur r + k = 25 + 3 * r + k := by
      intro r k; simp only [ChipTemplate.col0, walkTemplateHQK_baseCols]
    have hcolN : ∀ r k : ℕ, (walkTemplateHQK δF kroots).col0 3 .traceNext r + k = 25 + 3 * r + k := hcol0
    have hlimb : ∀ (i' : Fin n) (t : ℕ) (k : Fin 3), t < 10 →
        fullCol hn (colHQ δF kroots b col kLv vLv kRv vRv R) (136 + 3 * t + k) i' = coord b (roleVal δF R t i') k := by
      intro i' t k ht; have hk := k.isLt
      rw [hnew _ (by omega)]
      simp only [colHQ, extColF, new, hW]
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
        if_neg (by omega), if_neg (by omega), if_pos ⟨by omega, by omega⟩,
        show (136 + 3 * t + (k : ℕ) - 136) / 3 = t by omega]
      exact coordN_mod b _ _ k (by omega)
    set eK := gatherEnv b ((walkTemplateHQK δF kroots).col0 3) e1 with heK
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
       have hg' : g ∈ WChip.baseGates (F := F) kroots ++ baseHK := hg
       have hgb : g ∈ baseHK (F := F) := by
         rcases List.mem_append.mp hg' with h1 | h1
         · exact absurd h1 hg0
         · exact h1
       simp only [baseHK, List.mem_cons, List.not_mem_nil, or_false] at hgb
       rcases hgb with rfl | rfl
       · have h21 : e1.trace WalkHC.kL = kLv i := by
           show e1.trace 21 = _; rw [hET 21 (by omega), hkLc]
         rcases hkL i with h0 | h0 | h0 <;> simp [ternE, CoeffExpr.eval, cv, h21, h0]
       · have h23 : e1.trace WalkHC.kR = kRv i := by
           show e1.trace 23 = _; rw [hET 23 (by omega), hkRc]
         rcases hkR i with h0 | h0 | h0 <;> simp [ternE, CoeffExpr.eval, cv, h23, h0])
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
         · simp only [heK, gatherEnv, ChipTemplate.col0, walkTemplateHQK_baseCols]
           exact sum_slotVal b 25 WalkHQ.pubXQ pubs
         · simp only [heK, gatherEnv, ChipTemplate.col0, walkTemplateHQK_baseCols]
           exact sum_slotVal b 25 (WalkHQ.pubXQ + 1) pubs
       · rw [← hpubP]
         congr 1
         · simp only [heK, gatherEnv, ChipTemplate.col0, walkTemplateHQK_baseCols]
           exact sum_slotVal b 25 WalkHQ.pubPQ pubs
         · simp only [heK, gatherEnv, ChipTemplate.col0, walkTemplateHQK_baseCols]
           exact sum_slotVal b 25 (WalkHQ.pubPQ + 1) pubs)


end MainK

end

end Nock.NockVMROM.Thm54.VclL.Handle.WalkTraceHQ

/-! ## 4. The J-8 walk chip: the honest narrowed certificate -/

namespace Nock.NockVMROM.Thm54.VclL.Handle.HonestK8

open Nock Nock.Reified Nock.Framework Nock.Walk
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.WalkVCL
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.VclL.Handle Nock.NockVMROM.Thm54.VclL.Handle.CellTwinK
open Nock.NockVMROM.Thm54.VclL.Handle.WalkJ8
open Module
open scoped Polynomial

noncomputable section

section Cert8

/-- The honest narrowed certificate of a row of length `L ≤ 60`: `S = 60 − L = r + 29·b₅` with `r < 32`;
bit `i < 5` of `r`, and `b₅`. -/
def top8 (L : ℕ) : ℕ := if 32 ≤ 60 - L then 1 else 0
def rem8 (L : ℕ) : ℕ := 60 - L - 29 * top8 L
def certB8 (L i : ℕ) : ℕ := if i = 5 then top8 L else rem8 L / 2 ^ i % 2

theorem certB8_le (L i : ℕ) : certB8 L i ≤ 1 := by
  unfold certB8 top8
  split_ifs <;> omega

/-- The identity the narrowed gate asks for, `L + (b₀ + 2b₁ + 4b₂ + 8b₃ + 16b₄) + 29 b₅ = 60`. -/
theorem cert8_sum : ∀ L < 61, L + (certB8 L 0 + 2 * certB8 L 1 + 4 * certB8 L 2 + 8 * certB8 L 3 +
    16 * certB8 L 4) + 29 * certB8 L 5 = 60 := by decide

/-- The value in column `c ∈ [14, 21)`: `u = b₁ b₂` at `14`, bit `c − 15` at `15..20`. -/
def fixVal8 {F : Type} [Field F] (L c : ℕ) : F :=
  if c = 14 then ((certB8 L 1 * certB8 L 2 : ℕ) : F) else ((certB8 L (c - 15) : ℕ) : F)

/-- **The honest J-8 walk column function**: `colQ` with the certificate columns re-chosen. -/
def certUp {F : Type} [Field F] {n : ℕ} (colQ : ℕ → Fin n → F) (lenN : Fin n → ℕ) : ℕ → Fin n → F :=
  fun j i => if 14 ≤ j ∧ j < 21 then fixVal8 (lenN i) j else colQ j i

end Cert8

section Main8
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
  (δF : F) (kroots : ℕ) (b : Basis (Fin 3) F K) {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F)
  (orbit : StrictOrbitDomain F 3 h) (chals pubs : ℕ → K)
  (colQ : ℕ → Fin n → F) (lenN : Fin n → ℕ)

theorem walkChipJ8_accepts_honest (hinj : Function.Injective nodes)
    (hlen : ∀ i, colQ WChip.len i = (lenN i : F)) (hle : ∀ i, lenN i ≤ 60)
    (hsat : (walkChipHQK δF kroots b hn nodes orbit chals pubs).rap.Satisfies
      (honestQ hn nodes colQ _)) :
    (walkChipJ8 δF kroots b hn nodes orbit chals pubs).rap.Satisfies
      (honestQ hn nodes (certUp colQ lenN) _) := by
  have hs : (expandChip (walkTemplateHQK δF kroots) b (slotVal b 25 chals) (slotVal b 25 pubs) orbit
      (rowNodeSet nodes)).Satisfies (honestQ hn nodes colQ 166) := hsat
  show (expandChip (walkTemplateJ8 δF kroots) b (slotVal b 25 chals) (slotVal b 25 pubs) orbit
      (rowNodeSet nodes)).Satisfies (honestQ hn nodes (certUp colQ lenN) 166)
  erw [expandChip_satisfies_iff_language] at hs ⊢
  intro x hx
  obtain ⟨i, rfl⟩ := (mem_rowNodeSet_iff nodes x).mp hx
  obtain ⟨hb, -, -, hm⟩ := hs _ hx
  set eA := Reify.envOfTrace (honestQ hn nodes colQ 166) orbit.ω (nodes i) (slotVal b 25 chals)
    (slotVal b 25 pubs) with heA
  set eB := Reify.envOfTrace (honestQ hn nodes (certUp colQ lenN) 166) orbit.ω (nodes i)
    (slotVal b 25 chals) (slotVal b 25 pubs) with heB
  have hP : ∀ j : Fin 166, (j : ℕ) < 14 ∨ 21 ≤ (j : ℕ) →
      honestQ hn nodes colQ 166 j = honestQ hn nodes (certUp colQ lenN) 166 j := by
    intro j hj
    refine honestQ_congr hn nodes colQ _ 166 j ?_
    funext i'
    simp only [certUp]
    rw [if_neg (by omega)]
  have hA : AgreeOff eA eB := by
    refine ⟨fun j hj => ⟨?_, ?_⟩, rfl, rfl⟩
    · simp only [heA, heB, Reify.envOfTrace]
      split_ifs with h1
      · rw [hP ⟨j, h1⟩ hj]
      · rfl
    · simp only [heA, heB, Reify.envOfTrace]
      split_ifs with h1
      · rw [hP ⟨j, h1⟩ hj]
      · rfl
  have hon : ∀ c, 14 ≤ c → c < 21 → eB.trace c = fixVal8 (lenN i) c := by
    intro c h1 h2
    rw [heB, env_trace hn nodes hinj _ _ _ _ i (by omega)]
    simp only [fullCol, certUp]
    rw [if_neg (by omega), if_neg (by omega), if_pos ⟨h1, h2⟩]
  have hu : eB.trace 14 = ((certB8 (lenN i) 1 * certB8 (lenN i) 2 : ℕ) : F) := by
    rw [hon 14 (by omega) (by omega)]; simp [fixVal8]
  have hbit : ∀ k < 6, eB.trace (15 + k) = ((certB8 (lenN i) k : ℕ) : F) := by
    intro k hk; rw [hon (15 + k) (by omega) (by omega)]; simp only [fixVal8]; rw [if_neg (by omega)]
    congr 3; omega
  have hlenB : eB.trace 6 = ((lenN i : ℕ) : F) := by
    rw [← (hA.1 6 (by omega)).1, heA, env_trace hn nodes hinj _ _ _ _ i (by omega)]
    simp only [fullCol]
    rw [if_neg (by omega), if_neg (by omega)]; exact hlen i
  have hbA : ∀ g ∈ baseGatesJ8 (F := F) kroots ++ baseHK, avC g = true →
      g.eval eB = 0 ∨ g ∈ baseGatesJ8 (F := F) kroots ++ baseHK := fun g _ _ => Or.inr ‹_›
  have viaK : ∀ g, avC g = true →
      g ∈ (walkTemplateHQK δF kroots).baseTransition → g.eval eB = 0 :=
    fun g hav hmem => (avC_eval hA g hav).symm.trans (hb g hmem)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro g hg
    have hg' : g ∈ (basePre ++ [depthJ8] ++ basePost kroots) ++ baseHK := hg
    show g.eval eB = 0
    simp only [List.mem_append, List.mem_singleton] at hg'
    have hK : ∀ g, g ∈ (basePre ++ [exclOld, depthOld] ++ basePost kroots) ++ baseHK →
        g ∈ (walkTemplateHQK δF kroots).baseTransition := by
      intro g hg; exact (by rw [(walkJ8_unchanged δF kroots).1]; exact hg)
    rcases hg' with ((hg' | rfl) | hg') | hg'
    · simp only [basePre, List.mem_cons, List.not_mem_nil, or_false] at hg'
      rcases hg' with rfl | rfl | rfl | rfl
      · exact viaK _ (by simp [avC, cv, WChip.cL]) (hK _ (by simp [basePre]))
      · exact viaK _ (by simp [avC, cv, WChip.cR]) (hK _ (by simp [basePre]))
      · exact viaK _ (by simp [avC, cv, WChip.cR, WChip.cL, WChip.e]) (hK _ (by simp [basePre]))
      · have h1 := hbit 1 (by norm_num); have h2 := hbit 2 (by norm_num)
        simp only [CoeffExpr.eval, cv, WChip.bt, WChip.u, WChip.bit0]
        rw [hu, h1, h2]; push_cast; ring
    · simp only [depthJ8, CoeffExpr.eval, eval_bitSum, cv, WChip.len, WChip.bit0, WChip.bt]
      rw [hlenB]
      simp only [Finset.sum_range_succ, Finset.sum_range_zero]
      rw [hbit 0 (by norm_num), hbit 1 (by norm_num), hbit 2 (by norm_num), hbit 3 (by norm_num),
        hbit 4 (by norm_num), hbit 5 (by norm_num)]
      have e := cert8_sum (lenN i) (by have := hle i; omega)
      have e' : (((lenN i) + (certB8 (lenN i) 0 + 2 * certB8 (lenN i) 1 + 4 * certB8 (lenN i) 2 +
          8 * certB8 (lenN i) 3 + 16 * certB8 (lenN i) 4) + 29 * certB8 (lenN i) 5 : ℕ) : F) =
          ((60 : ℕ) : F) := by rw [e]
      push_cast at e'; linear_combination e'
    · simp only [basePost, List.mem_append, List.mem_map, List.mem_range] at hg'
      rcases hg' with hg' | ⟨k, hk, rfl⟩
      · exact viaK _ (basePost_av kroots g (by simpa [basePost] using hg'))
          (hK _ (by simp only [basePost, List.mem_append]; exact Or.inl (Or.inr (Or.inl hg'))))
      · have := hbit k hk
        simp only [boolE, CoeffExpr.eval, cv, WChip.bt, WChip.bit0]
        rw [this]
        rcases Nat.le_one_iff_eq_zero_or_eq_one.mp (certB8_le (lenN i) k) with h0 | h1
        · rw [h0]; simp
        · rw [h1]; simp
    · exact viaK _ (baseHK_av g hg') (by rw [(walkJ8_unchanged δF kroots).1]; simp [hg'])
  · intro g hg; exact absurd hg (by show g ∉ ([] : List (CoeffExpr F)); simp)
  · intro g hg; exact absurd hg (by show g ∉ (([] : List Expr) ++ [] ++ []); simp)
  · intro g hg
    have hg1 : g ∈ (walkTemplateHQK δF kroots).mixedTransition := hg
    have hav : avM g = true := by
      rcases List.mem_append.mp hg with hg | hg
      · exact walkMixed_av δF kroots g hg
      · exact walkHQ_av δF g hg
    have key := (avM_eval hA _ g hav).symm.trans (hm g hg1)
    have c1 : (walkTemplateHQK δF kroots).col0 3 = fun _ idx => 25 + 3 * idx := by
      funext k idx; simp [ChipTemplate.col0, walkTemplateHQK_baseCols]
    have c2 : (walkTemplateJ8 δF kroots).col0 3 = fun _ idx => 25 + 3 * idx := by
      funext k idx; simp [ChipTemplate.col0, walkTemplateJ8_baseCols]
    have hg2 : gatherEnv b ((walkTemplateHQK δF kroots).col0 3) eA =
        gatherEnv b ((walkTemplateJ8 δF kroots).col0 3) eB := by
      rw [c1, c2]
      unfold gatherEnv
      congr 1
      · funext idx; refine Finset.sum_congr rfl fun k _ => ?_
        exact congrArg (· • b k) (hA.1 (25 + 3 * idx + k) (by omega)).1
      · funext idx; refine Finset.sum_congr rfl fun k _ => ?_
        exact congrArg (· • b k) (hA.1 (25 + 3 * idx + k) (by omega)).2
    have hh := congrArg (fun E => g.eval E eB) hg2
    exact hh.symm.trans key

/-- **With the fixed preprocessing** (masks `0..2`): `honestQ` of the re-chosen certificate. -/
theorem walkChipJ8_accepts_honest_pp (hinj : Function.Injective nodes)
    (hlen : ∀ i, colQ WChip.len i = (lenN i : F)) (hle : ∀ i, lenN i ≤ 60)
    (hsat : RAP.SatisfiesWithPreprocessing (walkChipHQK δF kroots b hn nodes orbit chals pubs)
      (fun j => honestQ hn nodes colQ 166
        (Fin.cast (walkChipHQK_width δF kroots b hn nodes orbit chals pubs) j))) :
    RAP.SatisfiesWithPreprocessing (walkChipJ8 δF kroots b hn nodes orbit chals pubs)
      (fun j => honestQ hn nodes (certUp colQ lenN) 166
        (Fin.cast (walkChipJ8_width δF kroots b hn nodes orbit chals pubs) j)) := by
  refine ⟨walkChipJ8_accepts_honest δF kroots b hn nodes orbit chals pubs colQ lenN hinj hlen hle hsat.1, ?_⟩
  intro j
  fin_cases j
  · exact honestQ_zero hn nodes _ (by omega)
  · exact honestQ_one hn nodes _ (by omega)
  · have h2 := hsat.2 ⟨2, by show 2 < 3; omega⟩
    refine Eq.trans ?_ h2
    show honestQ hn nodes (certUp colQ lenN) 166 ⟨2, _⟩ = honestQ hn nodes colQ 166 ⟨2, _⟩
    refine honestQ_congr hn nodes _ _ _ _ ?_
    funext i'
    simp only [certUp]
    rw [if_neg (by omega)]

end Main8


section Pipeline8
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [Fintype K]
  (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))] (kroots : ℕ) (b : Basis (Fin 3) F K) {h n : ℕ}
  (hn : 0 < n) (nodes : Fin n → F) (orbit : StrictOrbitDomain F 3 h) (chals pubs : ℕ → K)
  (col : ℕ → Fin n → F) (kLv vLv kRv vRv : Fin n → F)

/-- **`walkChipHQK` accepts the honest trace with kinds in `{0,1,2}`, with its preprocessing**, from the
`ok`-gated original honest acceptance (the 40th's `walkTwinQ_accepted`, ternary kinds). -/
theorem walkTwinK_accepted (hinj : Function.Injective nodes)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω)
    (hok : RAP.SatisfiesWithPreprocessing (walkChipOk δF kroots b hn nodes orbit chals pubs true)
      (fun j => honestQ hn nodes col 132
        (Fin.cast (walkChipOk_w δF kroots b hn nodes orbit chals pubs true) j)))
    (hkL : ∀ i, kLv i = 0 ∨ kLv i = 1 ∨ kLv i = 2) (hkR : ∀ i, kRv i = 0 ∨ kRv i = 1 ∨ kRv i = 2)
    (hpX : ∀ i, WalkTraceHQ.dRow δF kroots b hn nodes orbit chals pubs WalkHC.xKeyH col kLv vLv kRv vRv i ≠ 0)
    (hpL : ∀ i, WalkTraceHQ.dRow δF kroots b hn nodes orbit chals pubs WalkHC.recLH col kLv vLv kRv vRv i ≠ 0)
    (hpR : ∀ i, WalkTraceHQ.dRow δF kroots b hn nodes orbit chals pubs WalkHC.recRH col kLv vLv kRv vRv i ≠ 0)
    (hpubX : Quad.mk _ (pubs WalkHQ.pubXQ) (pubs (WalkHQ.pubXQ + 1)) = ∑ j ∈ Finset.range n,
      (WalkTraceHQ.dN δF kroots b hn nodes orbit chals pubs col kLv vLv kRv vRv WalkHC.xKeyH j)⁻¹)
    (hpubP : Quad.mk _ (pubs WalkHQ.pubPQ) (pubs (WalkHQ.pubPQ + 1)) = ∑ j ∈ Finset.range n,
      (liftQ δF (WalkTraceH.cN j (col WChip.mL)) *
          (WalkTraceHQ.dN δF kroots b hn nodes orbit chals pubs col kLv vLv kRv vRv WalkHC.recLH j)⁻¹ +
        liftQ δF (WalkTraceH.cN j (col WChip.mR)) *
          (WalkTraceHQ.dN δF kroots b hn nodes orbit chals pubs col kLv vLv kRv vRv WalkHC.recRH j)⁻¹)) :
    RAP.SatisfiesWithPreprocessing (walkChipHQK δF kroots b hn nodes orbit chals pubs)
      (fun j => WalkTraceHQ.walkTraceHQ δF kroots b hn nodes orbit chals pubs col kLv vLv kRv vRv
        (Fin.cast (walkChipHQK_width δF kroots b hn nodes orbit chals pubs) j)) := by
  have hs := (walkChipOk_sat δF kroots b hn nodes orbit chals pubs true _ hok).2
  have hsat := WalkTraceHQ.walkChipHQK_accepts_honest δF kroots b hn nodes orbit chals pubs col kLv vLv kRv vRv
    hinj hadj hs.1 hkL hkR hpX hpL hpR hpubX hpubP
  refine ⟨hsat, ?_⟩
  intro j
  fin_cases j
  · exact honestQ_zero hn nodes _ (by rw [WalkTraceHQ.walkTemplateHQ_width]; omega)
  · exact honestQ_one hn nodes _ (by rw [WalkTraceHQ.walkTemplateHQ_width]; omega)
  · have h2 := hs.2 ⟨2, by show 2 < 3; omega⟩
    refine Eq.trans ?_ h2
    show honestQ hn nodes _ _ ⟨2, _⟩ = honestQ hn nodes col _ ⟨2, _⟩
    refine honestQ_congr hn nodes _ _ _ _ ?_
    funext i'
    simp [WalkTraceHQ.colHQ, extColF]

/-- **`walkChipJ8` accepts the honest trace at every row of length `≤ 60`, with its preprocessing**:
the 40th's honest walk trace, kinds `{0,1,2}`, the certificate columns re-chosen for the narrowed
gate. Every other column (including the round-1 `𝕂′` roles at `136..165`) is the honest one. -/
theorem walkTwinJ8_accepted (hinj : Function.Injective nodes)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω)
    (hok : RAP.SatisfiesWithPreprocessing (walkChipOk δF kroots b hn nodes orbit chals pubs true)
      (fun j => honestQ hn nodes col 132
        (Fin.cast (walkChipOk_w δF kroots b hn nodes orbit chals pubs true) j)))
    (hkL : ∀ i, kLv i = 0 ∨ kLv i = 1 ∨ kLv i = 2) (hkR : ∀ i, kRv i = 0 ∨ kRv i = 1 ∨ kRv i = 2)
    (hpX : ∀ i, WalkTraceHQ.dRow δF kroots b hn nodes orbit chals pubs WalkHC.xKeyH col kLv vLv kRv vRv i ≠ 0)
    (hpL : ∀ i, WalkTraceHQ.dRow δF kroots b hn nodes orbit chals pubs WalkHC.recLH col kLv vLv kRv vRv i ≠ 0)
    (hpR : ∀ i, WalkTraceHQ.dRow δF kroots b hn nodes orbit chals pubs WalkHC.recRH col kLv vLv kRv vRv i ≠ 0)
    (hpubX : Quad.mk _ (pubs WalkHQ.pubXQ) (pubs (WalkHQ.pubXQ + 1)) = ∑ j ∈ Finset.range n,
      (WalkTraceHQ.dN δF kroots b hn nodes orbit chals pubs col kLv vLv kRv vRv WalkHC.xKeyH j)⁻¹)
    (hpubP : Quad.mk _ (pubs WalkHQ.pubPQ) (pubs (WalkHQ.pubPQ + 1)) = ∑ j ∈ Finset.range n,
      (liftQ δF (WalkTraceH.cN j (col WChip.mL)) *
          (WalkTraceHQ.dN δF kroots b hn nodes orbit chals pubs col kLv vLv kRv vRv WalkHC.recLH j)⁻¹ +
        liftQ δF (WalkTraceH.cN j (col WChip.mR)) *
          (WalkTraceHQ.dN δF kroots b hn nodes orbit chals pubs col kLv vLv kRv vRv WalkHC.recRH j)⁻¹))
    (lenN : Fin n → ℕ) (hlen : ∀ i, col WChip.len i = (lenN i : F)) (hle : ∀ i, lenN i ≤ 60) :
    RAP.SatisfiesWithPreprocessing (walkChipJ8 δF kroots b hn nodes orbit chals pubs)
      (fun j => honestQ hn nodes
        (certUp (WalkTraceHQ.colHQ δF kroots b col kLv vLv kRv vRv
          (WalkTraceHQ.rolesF δF kroots b hn nodes orbit chals pubs col kLv vLv kRv vRv)) lenN) 166
        (Fin.cast (walkChipJ8_width δF kroots b hn nodes orbit chals pubs) j)) := by
  have hq := walkTwinK_accepted δF kroots b hn nodes orbit chals pubs col kLv vLv kRv vRv hinj hadj hok
    hkL hkR hpX hpL hpR hpubX hpubP
  refine walkChipJ8_accepts_honest_pp δF kroots b hn nodes orbit chals pubs _ lenN hinj ?_ hle hq
  intro i
  rw [← hlen i]
  simp [WalkTraceHQ.colHQ, extColF, WalkTraceHQ.new, WChip.len]

end Pipeline8

end

end Nock.NockVMROM.Thm54.VclL.Handle.HonestK8
