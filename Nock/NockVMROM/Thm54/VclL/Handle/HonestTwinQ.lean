/-
  Nock/NockVMROM/Thm54/VclL/Handle/HonestTwinQ.lean

  Additive: a NEW module; no existing module edited.

  `cellTwinQ_accepted` / `walkTwinQ_accepted`: the `𝕂′` twin of `TraceAcceptH.cellTwin_accepted` /
  `walkTwin_accepted`.  From the `ok`-gated original honest acceptance (the conclusion of
  `cell_acceptedW_genB` / `walk_acceptedW_gen`, at the VSQ challenge / public vectors), no vanishing `𝕂′`
  denominator and the `𝕂′` terminals equal to the totals, `cellChipHQ` / `walkChipHQ` accept
  `cellTraceHQ` / `walkTraceHQ` with their preprocessing.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.TraceAcceptH
import Nock.NockVMROM.Thm54.VclL.Handle.CellTraceHQ
import Nock.NockVMROM.Thm54.VclL.Handle.WalkTraceHQ

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

section CellQ
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [Fintype K]
  (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))] (b : Basis (Fin 3) F K) {h n : ℕ} (hn : 0 < n)
  (nodes : Fin n → F) (orbit : StrictOrbitDomain F 3 h) (chals pubs : ℕ → K)
  (col : ℕ → Fin n → F) (mhv : Fin n → F)

/-- **`cellTraceHQ` is accepted with its preprocessing**, from the `ok`-gated original honest acceptance. -/
theorem cellTwinQ_accepted (hinj : Function.Injective nodes)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω)
    (hok : RAP.SatisfiesWithPreprocessing (cellChipOk δF b hn nodes orbit chals pubs true)
      (fun j => honestQ hn nodes col 225
        (Fin.cast (cellChipOk_w δF b hn nodes orbit chals pubs true) j)))
    (hpole : ∀ i, CellTraceHQ.dRow δF b hn nodes orbit chals pubs col mhv i ≠ 0)
    (hpub : Quad.mk _ (pubs CellHQ.pubHQ) (pubs (CellHQ.pubHQ + 1)) = ∑ j ∈ Finset.range n,
      liftQ δF (CellTraceH.mN mhv j) * (CellTraceHQ.dN δF b hn nodes orbit chals pubs col mhv j)⁻¹) :
    RAP.SatisfiesWithPreprocessing (cellChipHQ δF b hn nodes orbit chals pubs)
      (fun j => CellTraceHQ.cellTraceHQ δF b hn nodes orbit chals pubs col mhv
        (Fin.cast (cellChipHQ_width δF b hn nodes orbit chals pubs) j)) := by
  have hs := (cellChipOk_sat δF b hn nodes orbit chals pubs true _ hok).2.1
  have hsat := CellTraceHQ.cellChipHQ_accepts_honest δF b hn nodes orbit chals pubs col mhv hinj hadj hs
    hpole hpub
  refine ⟨hsat, ?_⟩
  intro j
  fin_cases j
  · exact honestQ_zero hn nodes _ (by rw [CellTraceHQ.cellTemplateHQ_width]; omega)
  · exact honestQ_one hn nodes _ (by rw [CellTraceHQ.cellTemplateHQ_width]; omega)

end CellQ

section WalkQ
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [Fintype K]
  (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))] (kroots : ℕ) (b : Basis (Fin 3) F K) {h n : ℕ}
  (hn : 0 < n) (nodes : Fin n → F) (orbit : StrictOrbitDomain F 3 h) (chals pubs : ℕ → K)
  (col : ℕ → Fin n → F) (kLv vLv kRv vRv : Fin n → F)

/-- **`walkTraceHQ` is accepted with its preprocessing**, from the `ok`-gated original honest acceptance. -/
theorem walkTwinQ_accepted (hinj : Function.Injective nodes)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω)
    (hok : RAP.SatisfiesWithPreprocessing (walkChipOk δF kroots b hn nodes orbit chals pubs true)
      (fun j => honestQ hn nodes col 132
        (Fin.cast (walkChipOk_w δF kroots b hn nodes orbit chals pubs true) j)))
    (hkL : ∀ i, kLv i = 0 ∨ kLv i = 1) (hkR : ∀ i, kRv i = 0 ∨ kRv i = 1)
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
    RAP.SatisfiesWithPreprocessing (walkChipHQ δF kroots b hn nodes orbit chals pubs)
      (fun j => WalkTraceHQ.walkTraceHQ δF kroots b hn nodes orbit chals pubs col kLv vLv kRv vRv
        (Fin.cast (walkChipHQ_width δF kroots b hn nodes orbit chals pubs) j)) := by
  have hs := (walkChipOk_sat δF kroots b hn nodes orbit chals pubs true _ hok).2
  have hsat := WalkTraceHQ.walkChipHQ_accepts_honest δF kroots b hn nodes orbit chals pubs col kLv vLv kRv vRv
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

end WalkQ

end

end Nock.NockVMROM.Thm54.VclL.Handle
