import Nock.NockVMROM.Thm54.VclL.Compute.TowerJointSizes
import Nock.NockVMROM.Thm54.VclL.Compute.TowerHonestRun
import Nock.NockVMROM.Thm54.VclL.Compute.TowerRowFactsAt
import Nock.NockVMROM.Thm54.VclL.Chips.HonestVCLWReq
import Nock.NockVMROM.Thm54.VclL.Chips.MemSoundnessVCLW
import Nock.NockVMROM.Thm54.P8Core.SVFrame.StandaloneGeneric
import Nock.RedTeam.Batch1979Thm54WalkW4bCount
import Nock.NockVMROM.Thm54.VclL.Chips.Prelim
import Nock.NockVMROM.Thm54.VclL.Chips.StandaloneVCLW

/-!
# 1995): the joint compute–walk honest datum, the run builder and completeness

Twins of `TowerJointHonest`,
`TowerJointSizes`  and `TowerHonestRun`  with the WALK memory family
(`memSoundnessVCLW`, shape `shapeVW`) in place of the path family:

* `HonestVCLJW`: `HonestVCLT` at `shapeVW` plus the memory-shape fields (`hC0`, `hW0`: memory heights are
  the cell table and the walk table `walkRows (demT t)`, `hmnodes`, `hsizeM`).
* `jointMemW HJ …`: the walk memory datum of the SAME run, `kr := krW (demT t).cells (demT t).preads`;
  `hkp` (= `kr + |walk| < p`) is the `hmemW` content.  `jointMemW_honestV` (`rfl`) and
  `jointMemW_honestReq` (the request identity `HonestVCLW.req_eq`, `hslot` from the run, `demT_slot`): the
  compute side's `honestReqCF` is UNCHANGED.
* `vcl_completenessW'`: the frame's completeness at the pair.
-/

namespace Nock.NockVMROM.Thm54
namespace VclL.Compute
namespace TowerD

open Nock Nock.Walk Nock.Reified Module Polynomial
open Nock.NockVMROM.Thm54.SVFrame Nock.Framework
open Nock.NockVMROM.Thm54.T0Tower Nock.NockVMROM.Thm54.TraceGen
open Nock.NockVMROM.Thm54.VclL.Chips Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.VclL.GenWalk
open Nock.NockVMROM.Thm54.StrictExtension
open Nock.NockVMROM.Thm54.FiniteIO

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

noncomputable section

/-! ## 1. The joint datum -/

section Joint
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq F]
  [Fintype K] [DecidableEq K] [Fintype F] (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))]
  [Fact (ringChar F).Prime] [Algebra (ZMod (ringChar F)) K]
  (hT hP hC : ℕ)

/-- The walk-table length of a tree's demand. -/
def walkLen (t : NTree (GenComputeRow (Quad (algebraMap F K δF)))) : ℕ :=
  (walkRows (demT t).cells (demT t).preads).length

/-- The honest walk root count of a tree's demand. -/
def krT (t : NTree (GenComputeRow (Quad (algebraMap F K δF)))) : ℕ :=
  krW (demT t).cells (demT t).preads

/-- **The honest datum of the joint compute–walk run** (`HonestVCLJ`'s twin at `shapeVW`). -/
structure HonestVCLJW extends HonestVCLT F K δF hC (shapeVW hT hP) where
  hC0 : V.memRows (tCW hT hP) = (demT t).cells.length
  hW0 : V.memRows (tWW hT hP) = (walkRows (demT t).cells (demT t).preads).length
  hmnodes : ∀ (k : Fin (shapeVW hT hP).k) (i : Fin (V.memRows k)), V.memNodes k i = (V.orbitM k).ω ^ (i : ℕ)
  hsizeM : ∀ k : Fin (shapeVW hT hP).k, V.memRows k ≤ 2 ^ ((shapeVW hT hP).table k).height

variable {δF hT hP hC}

theorem HonestVCLJW.hadj (HJ : HonestVCLJW (K := K) δF hT hP hC) (k : Fin (shapeVW hT hP).k) :
    HJ.V.AdjacentM k := by
  intro i hi
  rw [HJ.hmnodes k ⟨(i : ℕ) + 1, hi⟩, HJ.hmnodes k i]
  exact pow_succ _ _

theorem HonestVCLJW.hinj (HJ : HonestVCLJW (K := K) δF hT hP hC) (k : Fin (shapeVW hT hP).k) :
    Function.Injective (HJ.V.memNodes k) := by
  intro a b hab
  rw [HJ.hmnodes k a, HJ.hmnodes k b] at hab
  have hord : orderOf (HJ.V.orbitM k).ω = 3 * 2 ^ ((shapeVW hT hP).table k).height :=
    (HJ.V.orbitM k).order_ω
  have hle := HJ.hsizeM k
  apply Fin.ext
  refine pow_injOn_Iio_orderOf ?_ ?_ hab
  · show (a : ℕ) < orderOf _
    rw [hord]; have := a.isLt; omega
  · show (b : ℕ) < orderOf _
    rw [hord]; have := b.isLt; omega

/-- **The joint builder**: the walk memory datum of the SAME run (`V := HJ.V`, `d := demT HJ.t`,
`kr := krW`), from the field parameters and the public size conditions (`hmemRows`, `hkp` from `hmemC`,
`hmemW`). -/
def jointMemW (HJ : HonestVCLJW (K := K) δF hT hP hC)
    (hF : GeneratedField.PrimeFieldElems F) (hq : 2 ^ 63 < ringChar F)
    (hleaf : programLeafBound (airReorder HJ.t) ≤ 2 ^ 110)
    (hmemRows : ∀ k, HJ.V.memRows k + 1 < ringChar F)
    (haxis : programAxisBound (airReorder HJ.t) < 2 ^ 63)
    (hkp : krT δF HJ.t + HJ.V.memRows (tWW hT hP) < ringChar F) :
    HonestVCLW (K := K) δF hT hP hC (krT δF HJ.t) where
  V := HJ.V
  d := demT HJ.t
  hF := hF
  hq := hq
  hrows := hmemRows
  hadj := HJ.hadj
  hinj := HJ.hinj
  hrank := demT_rank_lt δF HJ.hgen hleaf
  h62 := fun r hr => by
    have : r ∈ (demT HJ.t).reads ∨ r ∈ (demT HJ.t).preads := by
      unfold pathReads at hr
      exact Or.inr (List.mem_filter.mp (List.mem_dedup.mp hr)).1
    exact demT_depth_le δF HJ.hgen haxis r this
  hC0 := HJ.hC0
  hW0 := HJ.hW0
  hkr := rfl
  hkp := hkp

end Joint

/-! ## 2. The request identity at the closed form -/

section Req
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq F]
  [Fintype K] [DecidableEq K] [Fintype F] {δF : F} [Fact (¬ IsSquare (algebraMap F K δF))]
  [Fact (ringChar F).Prime] [Algebra (ZMod (ringChar F)) K] {hT hP hC kr : ℕ}

/-- **The walk family's honest requests are the compute side's closed form `honestReqCF`.** -/
theorem HonestVCLW.req_eq_CF (H : HonestVCLW (K := K) δF hT hP hC kr) (χ : Coins frameVCL K)
    (hslot : ∀ r ∈ pathReads H.d.preads, (Noun.slot r.2 r.1).isSome) (a : Fin 3) :
    H.req χ a = honestReqCF (γC χ) (ρC χ) (zC χ) H.d.cells H.d.preads H.d.reads a := by
  obtain ⟨h0, h1, h2⟩ := H.req_eq χ hslot
  fin_cases a
  · exact h0
  · exact h1
  · exact h2

end Req

section Joint2
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq F]
  [Fintype K] [DecidableEq K] [Fintype F] (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))]
  [Fact (ringChar F).Prime] [Algebra (ZMod (ringChar F)) K]
  {hT hP hC : ℕ}

/-- **`honestV_eq`**: the two honest verifier data are the same. -/
theorem jointMemW_honestV (HJ : HonestVCLJW (K := K) δF hT hP hC)
    (hF : GeneratedField.PrimeFieldElems F) (hq : 2 ^ 63 < ringChar F)
    (hleaf : programLeafBound (airReorder HJ.t) ≤ 2 ^ 110)
    (hmemRows : ∀ k, HJ.V.memRows k + 1 < ringChar F)
    (haxis : programAxisBound (airReorder HJ.t) < 2 ^ 63)
    (hkp : krT δF HJ.t + HJ.V.memRows (tWW hT hP) < ringChar F) :
    (compSoundnessVCLT F K hC (shapeVW hT hP) δF).honestV HJ.toHonestVCLT =
      (memSoundnessVCLW (K := K) δF hT hP (krT δF HJ.t) (hC := hC) (C := tableVCLT hC)).honestV
        (jointMemW HJ hF hq hleaf hmemRows haxis hkp) := rfl

/-- **`honestReq_eq`**: the two honest request vectors agree at every coin vector and accumulator. -/
theorem jointMemW_honestReq (HJ : HonestVCLJW (K := K) δF hT hP hC)
    (hF : GeneratedField.PrimeFieldElems F) (hq : 2 ^ 63 < ringChar F)
    (hleaf : programLeafBound (airReorder HJ.t) ≤ 2 ^ 110)
    (hmemRows : ∀ k, HJ.V.memRows k + 1 < ringChar F)
    (haxis : programAxisBound (airReorder HJ.t) < 2 ^ 63)
    (hkp : krT δF HJ.t + HJ.V.memRows (tWW hT hP) < ringChar F) :
    (compSoundnessVCLT F K hC (shapeVW hT hP) δF).honestReq HJ.toHonestVCLT =
      (memSoundnessVCLW (K := K) δF hT hP (krT δF HJ.t) (hC := hC) (C := tableVCLT hC)).honestReq
        (jointMemW HJ hF hq hleaf hmemRows haxis hkp) := by
  funext χ a
  show reqT HJ.t χ a = (jointMemW HJ hF hq hleaf hmemRows haxis hkp).req χ a
  rw [HonestVCLW.req_eq_CF (jointMemW HJ hF hq hleaf hmemRows haxis hkp) χ (demT_slot_of_gen δF HJ.hgen) a]
  rfl

end Joint2

/-! ## 3. The standalone premises at the walk family -/

section Premises
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq F]
  [Fintype K] [DecidableEq K] [Fintype F] (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))]
  [Fact (ringChar F).Prime] [Algebra (ZMod (ringChar F)) K]
  (hT hP hC kr : ℕ)


/-- The UNCHANGED tower compute family, at the walk memory shape (= `StandaloneW.CFvW`). -/
abbrev CFvW4 : CompSoundnessFamily F K (Quad (algebraMap F K δF)) (Quad (algebraMap F K δF)) VclL.RV.KeyVCL
    frameVCL hC (shapeVW hT hP) (tableVCLT hC) 3 (m := VclL.RV.mVCL)
    (VclL.RV.recordViewVCL F K (Quad (algebraMap F K δF)) (tableVCLT hC) (shapeVW hT hP) hC)
    (ChipRAP.seedSpecVCL (algebraMap F K δF)) (ioSpecVCLQuad (algebraMap F K δF)) :=
  StandaloneW.CFvW δF hT hP hC

abbrev MFvW4 : MemSoundnessFamily F K (Quad (algebraMap F K δF)) (Quad (algebraMap F K δF)) VclL.RV.KeyVCL
    frameVCL hC (shapeVW hT hP) (tableVCLT hC) 3 (m := VclL.RV.mVCL)
    (VclL.RV.recordViewVCL F K (Quad (algebraMap F K δF)) (tableVCLT hC) (shapeVW hT hP) hC)
    (ChipRAP.seedSpecVCL (algebraMap F K δF)) (ioSpecVCLQuad (algebraMap F K δF)) :=
  StandaloneW.MFvW δF hT hP hC kr

theorem decodedNounW_bounded4 (V : VerifierData F K hC (shapeVW hT hP))
    (b : ∀ t : Fin (shapeVW hT hP).k, B0Cols F ((shapeVW hT hP).table t)) (i : ℕ) :
    FieldEmbedding.BoundedBy (ringChar F) (decodedNounW hT hP V b i) :=
  StandaloneW.decodedNounW_bounded hT hP hC V b i

/-- `ExtraPremises` at the compute family and the walk memory family (= `StandaloneW.extraPremises_vclW`). -/
theorem extraPremises_vclW4 :
    ExtraPremises (CFvW4 (K := K) δF hT hP hC) (MFvW4 (K := K) δF hT hP hC kr) :=
  StandaloneW.extraPremises_vclW δF hT hP hC kr

/-- (= `StandaloneW.rowFactsAt_CFvW`.) -/
theorem rowFactsAt_CFvW4 : rowFactsAt (CFvW4 (K := K) δF hT hP hC) :=
  StandaloneW.rowFactsAt_CFvW δF hT hP hC

end Premises

/-! ## 4. Completeness at the compute family and the walk family -/

section Complete
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq F]
  [Fintype K] [DecidableEq K] [Fintype F] (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))]
  [Fact (ringChar F).Prime] [Algebra (ZMod (ringChar F)) K]
  (hT hP hC : ℕ)

open Classical in
/-- **Completeness at the compute family and the walk family** (twin of `Batch1938.vcl_completeness'`).
Parameters `hF`, `hq`; public size conditions `hleaf`, `hmemRows`, `haxis`, and `hkp` (the walk bound). -/
theorem vcl_completenessW' (HJ : HonestVCLJW (K := K) δF hT hP hC)
    (hF : GeneratedField.PrimeFieldElems F) (hq : 2 ^ 63 < ringChar F)
    (hleaf : programLeafBound (airReorder HJ.t) ≤ 2 ^ 110)
    (hmemRows : ∀ k, HJ.V.memRows k + 1 < ringChar F)
    (haxis : programAxisBound (airReorder HJ.t) < 2 ^ 63)
    (hkp : krT δF HJ.t + HJ.V.memRows (tWW hT hP) < ringChar F) :
    ((Finset.univ.filter fun χ : Coins frameVCL K =>
        ∃ s ∈ (CFvW4 (K := K) δF hT hP hC).honestBad HJ.toHonestVCLT ++
            (MFvW4 (K := K) δF hT hP hC (krT δF HJ.t)).honestBad
              (jointMemW HJ hF hq hleaf hmemRows haxis hkp),
          s.mem ((CFvW4 (K := K) δF hT hP hC).honestQ HJ.toHonestVCLT χ,
            (MFvW4 (K := K) δF hT hP hC (krT δF HJ.t)).honestQ
              (jointMemW HJ hF hq hleaf hmemRows haxis hkp) χ) χ).card : ℚ) /
        Fintype.card (Coins frameVCL K) ≤
      epsilonOf ((CFvW4 (K := K) δF hT hP hC).honestBad HJ.toHonestVCLT ++
        (MFvW4 (K := K) δF hT hP hC (krT δF HJ.t)).honestBad
          (jointMemW HJ hF hq hleaf hmemRows haxis hkp)) :=
  (SVFrame.standalone_generic (rowFactsAt_CFvW4 δF hT hP hC)
    (extraPremises_vclW4 δF hT hP hC (krT δF HJ.t))).completeness
    HJ.toHonestVCLT (jointMemW HJ hF hq hleaf hmemRows haxis hkp)
    (jointMemW_honestV δF HJ hF hq hleaf hmemRows haxis hkp)
    (jointMemW_honestReq δF HJ hF hq hleaf hmemRows haxis hkp)

end Complete

/-! ## 5. The run builder at the walk shape -/

section Build
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq F]
  [Fintype K] [DecidableEq K] [Fintype F] (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))]
  [Fact (ringChar F).Prime] [Algebra (ZMod (ringChar F)) K]
  (hT hP hC : ℕ)

theorem walkLen_pos (t : NTree (GenComputeRow (Quad (algebraMap F K δF)))) : 0 < walkLen (K := K) δF t := by
  have h1 := one_le_krW (demT t).cells (demT t).preads
  have h2 := krW_le_rows (demT t).cells (demT t).preads
  unfold walkLen; omega

theorem shapeVW_height (k : Fin (shapeVW hT hP).k) :
    ((shapeVW hT hP).table k).height = if (k : ℕ) = 0 then hT else hP := by
  show (if (k : ℕ) = 0 then _ else _ : TableSpec).height = _
  split_ifs <;> rfl

/-- The memory orbits of the walk shape, per table. -/
def orbitMOfW (hT1 : 1 ≤ hT) (hP1 : 1 ≤ hP)
    (hFT : 3 * 2 ^ hT ∣ Fintype.card F - 1) (hFP : 3 * 2 ^ hP ∣ Fintype.card F - 1)
    (k : Fin (shapeVW hT hP).k) : StrictOrbitDomain F 3 ((shapeVW hT hP).table k).height :=
  strictOrbitOf _ (by rw [shapeVW_height]; split_ifs <;> assumption)
    (by rw [shapeVW_height]; split_ifs <;> assumption)

/-- **The verifier datum of the run at the walk shape**: memory rows = cell table, walk table. -/
def vOfRunW {fuel : ℕ} {subject formula result : Noun}
    (hrun : Nock.evalN fuel subject formula = some result)
    (hbound : RunBoundedBy (ringChar F) fuel subject formula)
    (Ksz : ℕ) (hK3 : Module.finrank F K = 3)
    (hC1 : 1 ≤ hC) (hT1 : 1 ≤ hT) (hP1 : 1 ≤ hP)
    (hFC : 3 * 2 ^ hC ∣ Fintype.card F - 1) (hFT : 3 * 2 ^ hT ∣ Fintype.card F - 1)
    (hFP : 3 * 2 ^ hP ∣ Fintype.card F - 1) :
    VerifierData F K hC (shapeVW hT hP) where
  claim := ⟨subject, formula, result⟩
  N := nRows (runTree (K := K) δF hrun hbound)
  hN := nRows_pos δF _
  Ksz := Ksz
  basis := Module.finBasisOfFinrankEq F K hK3
  orbitC := strictOrbitOf hC hC1 hFC
  computeNodes i := (strictOrbitOf hC hC1 hFC).ω ^ (i : ℕ)
  memRows k := if (k : ℕ) = 0 then cellLen (K := K) δF (runTree (K := K) δF hrun hbound)
    else walkLen (K := K) δF (runTree (K := K) δF hrun hbound)
  hM k := by
    split_ifs
    · exact demT_cells_pos δF (romTree_spec _) (formula_cell_of_evalN hrun)
    · exact walkLen_pos δF _
  orbitM := orbitMOfW hT hP hT1 hP1 hFT hFP
  memNodes k i := (orbitMOfW hT hP hT1 hP1 hFT hFP k).ω ^ (i : ℕ)

/-- **`HonestVCLJW` from the compiler run.** -/
def honestVCLJW_of_run {fuel : ℕ} {subject formula result : Noun}
    (hrun : Nock.evalN fuel subject formula = some result)
    (hbound : RunBoundedBy (ringChar F) fuel subject formula)
    (Ksz : ℕ) (αs : Quad (algebraMap F K δF)) (hK3 : Module.finrank F K = 3)
    (hp : 25 ≤ ringChar F)
    (hC1 : 1 ≤ hC) (hT1 : 1 ≤ hT) (hP1 : 1 ≤ hP)
    (hFC : 3 * 2 ^ hC ∣ Fintype.card F - 1) (hFT : 3 * 2 ^ hT ∣ Fintype.card F - 1)
    (hFP : 3 * 2 ^ hP ∣ Fintype.card F - 1)
    (hsize : nRows (runTree (K := K) δF hrun hbound) ≤ 2 ^ hC)
    (hrowsC : 3 * nRows (runTree (K := K) δF hrun hbound) < ringChar K)
    (hsizeT : cellLen (K := K) δF (runTree (K := K) δF hrun hbound) ≤ 2 ^ hT)
    (hsizeP : pathLen (K := K) δF (runTree (K := K) δF hrun hbound) ≤ 2 ^ hP) :
    HonestVCLJW (K := K) δF hT hP hC where
  V := vOfRunW δF hT hP hC hrun hbound Ksz hK3 hC1 hT1 hP1 hFC hFT hFP
  fuel := fuel
  t := runTree δF hrun hbound
  hgen := romTree_spec _
  αs := αs
  hN := rfl
  hnodes _ := rfl
  hsize := hsize
  hp := hp
  hrowsC := hrowsC
  hC0 := by simp [vOfRunW, tCW, cellLen]
  hW0 := by simp [vOfRunW, tWW, walkLen]
  hmnodes _ _ := rfl
  hsizeM k := by
    show (if (k : ℕ) = 0 then _ else _) ≤ 2 ^ ((shapeVW hT hP).table k).height
    rw [shapeVW_height]
    split_ifs
    · exact hsizeT
    · exact (Nock.RedTeam.Batch1979.walkLen_le_pathLen δF (romTree_spec _)).trans hsizeP

/-- `hmemRows` from `hmemC` and the walk bound `hmemW` (`krW ≥ 1`). -/
theorem memRowsW_of_run {fuel : ℕ} {subject formula result : Noun}
    (hrun : Nock.evalN fuel subject formula = some result)
    (hbound : RunBoundedBy (ringChar F) fuel subject formula)
    (Ksz : ℕ) (hK3 : Module.finrank F K = 3)
    (hC1 : 1 ≤ hC) (hT1 : 1 ≤ hT) (hP1 : 1 ≤ hP)
    (hFC : 3 * 2 ^ hC ∣ Fintype.card F - 1) (hFT : 3 * 2 ^ hT ∣ Fintype.card F - 1)
    (hFP : 3 * 2 ^ hP ∣ Fintype.card F - 1)
    (hmemC : cellLen (K := K) δF (runTree (K := K) δF hrun hbound) + 1 < ringChar F)
    (hmemW : krT (K := K) δF (runTree (K := K) δF hrun hbound) +
      walkLen (K := K) δF (runTree (K := K) δF hrun hbound) < ringChar F) :
    ∀ k, (vOfRunW (K := K) δF hT hP hC hrun hbound Ksz hK3 hC1 hT1 hP1 hFC hFT hFP).memRows k + 1
      < ringChar F := by
  intro k
  show (if (k : ℕ) = 0 then _ else _) + 1 < _
  have h1 := one_le_krW (demT (runTree (K := K) δF hrun hbound)).cells (demT (runTree (K := K) δF hrun hbound)).preads
  split_ifs
  · exact hmemC
  · unfold krT at hmemW; omega

/-- `hkp` of the joint datum from the walk bound `hmemW`. -/
theorem kpW_of_run {fuel : ℕ} {subject formula result : Noun}
    (hrun : Nock.evalN fuel subject formula = some result)
    (hbound : RunBoundedBy (ringChar F) fuel subject formula)
    (Ksz : ℕ) (hK3 : Module.finrank F K = 3)
    (hC1 : 1 ≤ hC) (hT1 : 1 ≤ hT) (hP1 : 1 ≤ hP)
    (hFC : 3 * 2 ^ hC ∣ Fintype.card F - 1) (hFT : 3 * 2 ^ hT ∣ Fintype.card F - 1)
    (hFP : 3 * 2 ^ hP ∣ Fintype.card F - 1)
    (hmemW : krT (K := K) δF (runTree (K := K) δF hrun hbound) +
      walkLen (K := K) δF (runTree (K := K) δF hrun hbound) < ringChar F) :
    krT (K := K) δF (runTree (K := K) δF hrun hbound) +
      (vOfRunW (K := K) δF hT hP hC hrun hbound Ksz hK3 hC1 hT1 hP1 hFC hFT hFP).memRows (tWW hT hP)
      < ringChar F := hmemW

end Build

end

end TowerD
end VclL.Compute
end Nock.NockVMROM.Thm54
