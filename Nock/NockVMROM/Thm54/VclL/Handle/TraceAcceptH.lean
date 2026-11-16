/-
  Nock/NockVMROM/Thm54/VclL/Handle/TraceAcceptH.lean

  Additive.

  `cellTwin_accepted` / `walkTwin_accepted`: if the `ok`-gated original chip accepts the honest
  `honestQ` trace of `col` (the conclusion of `cell_acceptedW` / `walk_acceptedW`), then the twin
  accepts `cellTraceH` / `walkTraceH` with its preprocessing, under the side conditions of
  `cellChipH_accepts_honest` / `walkChipH_accepts_honest`.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.WalkTraceH

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

section Cell
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
  (δF : F) (b : Basis (Fin 3) F K) {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F)
  (orbit : StrictOrbitDomain F 3 h) (chals pubs : ℕ → K)
  (col : ℕ → Fin n → F) (mhv : Fin n → F)

/-- **`cellTraceH` is accepted with its preprocessing**, from the `ok`-gated original honest acceptance. -/
theorem cellTwin_accepted (hinj : Function.Injective nodes)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω)
    (hok : RAP.SatisfiesWithPreprocessing (cellChipOk δF b hn nodes orbit chals pubs true)
      (fun j => honestQ hn nodes col 225
        (Fin.cast (cellChipOk_w δF b hn nodes orbit chals pubs true) j)))
    (hpole : ∀ i, CellTraceH.dRow δF b hn nodes orbit chals pubs col mhv i ≠ 0)
    (hpub : pubs CellH.pubH = ∑ j ∈ Finset.range n,
      algebraMap F K (CellTraceH.mN mhv j) * (CellTraceH.dN δF b hn nodes orbit chals pubs col mhv j)⁻¹) :
    RAP.SatisfiesWithPreprocessing (cellChipH δF b hn nodes orbit chals pubs)
      (fun j => CellTraceH.cellTraceH δF b hn nodes orbit chals pubs col mhv
        (Fin.cast (cellChipH_width δF b hn nodes orbit chals pubs) j)) := by
  have hs := (cellChipOk_sat δF b hn nodes orbit chals pubs true _ hok).2.1
  have hsat := CellTraceH.cellChipH_accepts_honest δF b hn nodes orbit chals pubs col mhv hinj hadj hs
    hpole hpub
  refine ⟨hsat, ?_⟩
  intro j
  fin_cases j
  · exact honestQ_zero hn nodes _ (by rw [CellTraceH.cellTemplateH_width]; omega)
  · exact honestQ_one hn nodes _ (by rw [CellTraceH.cellTemplateH_width]; omega)

end Cell

section Walk
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
  (δF : F) (kroots : ℕ) (b : Basis (Fin 3) F K) {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F)
  (orbit : StrictOrbitDomain F 3 h) (chals pubs : ℕ → K)
  (col : ℕ → Fin n → F) (kLv vLv kRv vRv : Fin n → F)

/-- **`walkTraceH` is accepted with its preprocessing**, from the `ok`-gated original honest acceptance. -/
theorem walkTwin_accepted (hinj : Function.Injective nodes)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω)
    (hok : RAP.SatisfiesWithPreprocessing (walkChipOk δF kroots b hn nodes orbit chals pubs true)
      (fun j => honestQ hn nodes col 132
        (Fin.cast (walkChipOk_w δF kroots b hn nodes orbit chals pubs true) j)))
    (hkL : ∀ i, kLv i = 0 ∨ kLv i = 1) (hkR : ∀ i, kRv i = 0 ∨ kRv i = 1)
    (hpX : ∀ i, WalkTraceH.dRow δF kroots b hn nodes orbit chals pubs WalkHC.xKeyH col kLv vLv kRv vRv i ≠ 0)
    (hpL : ∀ i, WalkTraceH.dRow δF kroots b hn nodes orbit chals pubs WalkHC.recLH col kLv vLv kRv vRv i ≠ 0)
    (hpR : ∀ i, WalkTraceH.dRow δF kroots b hn nodes orbit chals pubs WalkHC.recRH col kLv vLv kRv vRv i ≠ 0)
    (hpubX : pubs WalkHC.pubX = ∑ j ∈ Finset.range n,
      (WalkTraceH.dN δF kroots b hn nodes orbit chals pubs col kLv vLv kRv vRv WalkHC.xKeyH j)⁻¹)
    (hpubP : pubs WalkHC.pubP = ∑ j ∈ Finset.range n,
      (algebraMap F K (WalkTraceH.cN j (col WChip.mL)) *
          (WalkTraceH.dN δF kroots b hn nodes orbit chals pubs col kLv vLv kRv vRv WalkHC.recLH j)⁻¹ +
        algebraMap F K (WalkTraceH.cN j (col WChip.mR)) *
          (WalkTraceH.dN δF kroots b hn nodes orbit chals pubs col kLv vLv kRv vRv WalkHC.recRH j)⁻¹)) :
    RAP.SatisfiesWithPreprocessing (walkChipH δF kroots b hn nodes orbit chals pubs)
      (fun j => WalkTraceH.walkTraceH δF kroots b hn nodes orbit chals pubs col kLv vLv kRv vRv
        (Fin.cast (walkChipH_width δF kroots b hn nodes orbit chals pubs) j)) := by
  have hs := (walkChipOk_sat δF kroots b hn nodes orbit chals pubs true _ hok).2
  have hsat := WalkTraceH.walkChipH_accepts_honest δF kroots b hn nodes orbit chals pubs col kLv vLv kRv vRv
    hinj hadj hs.1 hkL hkR hpX hpL hpR hpubX hpubP
  refine ⟨hsat, ?_⟩
  intro j
  fin_cases j
  · exact honestQ_zero hn nodes _ (by rw [WalkTraceH.walkTemplateH_width]; omega)
  · exact honestQ_one hn nodes _ (by rw [WalkTraceH.walkTemplateH_width]; omega)
  · have h2 := hs.2 ⟨2, by show 2 < 3; omega⟩
    refine Eq.trans ?_ h2
    show honestQ hn nodes _ _ ⟨2, _⟩ = honestQ hn nodes col _ ⟨2, _⟩
    refine honestQ_congr hn nodes _ _ _ _ ?_
    funext i'
    simp [WalkTraceH.colH, extColF]

end Walk

end

end Nock.NockVMROM.Thm54.VclL.Handle
