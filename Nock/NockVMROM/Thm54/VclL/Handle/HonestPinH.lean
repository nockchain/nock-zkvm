/-
  Nock/NockVMROM/Thm54/VclL/Handle/HonestPinH.lean

  Additive; no handle accumulator, coin or IO summand is touched.

  * `runRowsH t = bfsRows (airReorder t)`: the compute rows of a run, over which the honest datum's demand
    is `demandH2`.
  * `computeChipVCLH_honest_sat_VS_pinned`: the VS compute-chip satisfaction with the cell list
    `cells := H.d.cells` of the memory datum `H` (`H.d = demandH2 (runRowsH t)`), so the compute side's
    serials `idxOf … cells` and the memory side's cell-table serials are positions in ONE list.
  * `hcomp_pinned`: the hypothesis `hcomp` of `honest_accepted_VS'` from the same lemma, given that the
    message's compute trace polynomials are `compPoly … H.d.cells …`.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.HonestAcceptedVSB
import Nock.NockVMROM.Thm54.VclL.Handle.HonestDemand2
import Nock.NockVMROM.Thm54.TraceGen.GenGenericBounded
import Nock.NockVMROM.Thm54.TraceGen.GenSubISAWindow

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Nock.NockVMROM.Thm54.VclL.Handle.FrameVS

open Nock Nock.Reified Nock.Framework Nock.Walk
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.SVFrame Nock.NockVMROM.Thm54.SVFrameG
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.VclL.GenWalk Nock.NockVMROM.Thm54.TraceGen
open Nock.NockVMROM.Thm54.SemanticStrategy
open Module
open scoped Polynomial

noncomputable section

/-! ## 1. `hat` from the run -/

section Hat
variable {Kg : Type} [Field Kg]

theorem atomsLt_of_boundedBy {q : ℕ} : ∀ n : Noun, FieldEmbedding.BoundedBy q n → AtomsLt q n
  | .atom k, h => by intro j hj; simp [Noun.leafList] at hj; subst hj; exact h
  | .cell a b, h => by
    intro j hj
    simp only [Noun.leafList, List.mem_append] at hj
    rcases hj with hj | hj
    · exact atomsLt_of_boundedBy a h.1 j hj
    · exact atomsLt_of_boundedBy b h.2 j hj

theorem childT_bounded {q : ℕ} (hq : 0 < q) {sk : ComputeRowSkeleton} (hb : sk.BoundedBy q)
    (i : Fin 3) (slot : TripleSlot) : FieldEmbedding.BoundedBy q (childT sk i slot) := by
  unfold childT
  split_ifs with h
  · exact hb.2.2.2.2.1 i h slot
  · exact hq

/-- Both subformula-result handles of a row are bounded when the skeleton is. -/
theorem rowOfSkelH_sf_bounded {q : ℕ} (hq : 0 < q) {sk : ComputeRowSkeleton} (hb : sk.BoundedBy q) :
    FieldEmbedding.BoundedBy q (rowOfSkelH sk).sf1 ∧ FieldEmbedding.BoundedBy q (rowOfSkelH sk).sf2 := by
  rw [rH_sf1, rH_sf2]
  have h0 := childT_bounded hq hb 0 .result
  have h1 := childT_bounded hq hb 1 .result
  have ha : FieldEmbedding.BoundedBy q (.atom 0 : Noun) := hq
  unfold rowOfSkel
  split <;> exact ⟨by assumption, by assumption⟩

/-- **`hat` from the run.**  With `RunBoundedBy q` and bounded claim operands, every honest row of the
compiler's AIR-reordered tree has atoms `< q` in its two subformula-result handles. -/
theorem hat_of_run {q fuel : ℕ} (hq : 1 < q) {subject formula result : Noun}
    {t : NTree (GenComputeRow Kg)}
    (hrun : Nock.evalN fuel subject formula = some result)
    (hbound : RunBoundedBy q fuel subject formula)
    (hs : FieldEmbedding.BoundedBy q subject) (hf : FieldEmbedding.BoundedBy q formula)
    (hgen : genComputeSkeleton (K := Kg) fuel subject formula = .ok (t, result)) :
    ∀ g ∈ bfsRows (airReorder t),
      AtomsLt q (rowOfSkelH g.skel).sf1 ∧ AtomsLt q (rowOfSkelH g.skel).sf2 := by
  have hG := evalGRom_le_evalGBy (evalGRom_of_runBounded hrun hbound)
  have hnb := genComputeSkeleton_airReorder_inTree_bounded hq hs hf hG hgen
  refine (forall_bfsRows_iff (airReorder t)).mpr ?_
  intro u hu
  have hb := (hnb u hu).1
  have := rowOfSkelH_sf_bounded (q := q) (by omega) hb
  exact ⟨atomsLt_of_boundedBy _ this.1, atomsLt_of_boundedBy _ this.2⟩

end Hat

/-! ## 2. One cell list -/

section Pin
variable {F K Kg : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq F]
  [Fintype K] [DecidableEq K] [Fintype F] [Fact (ringChar F).Prime] [Algebra (ZMod (ringChar F)) K]
  [Field Kg] {δF : F} [Fact (¬ IsSquare (algebraMap F K δF))] [DecidableEq (Quad (algebraMap F K δF))]
  {hT hP hC kr : ℕ}

/-- The compute rows of a run (the BFS rows of the AIR-reordered tree). -/
def runRowsH (t : NTree (GenComputeRow Kg)) : List (GenComputeRow Kg) := bfsRows (airReorder t)

theorem pinned_cells {t : NTree (GenComputeRow Kg)} (H : HonestVCLW (K := K) δF hT hP hC kr)
    (hd : H.d = demandH2 (runRowsH t)) : H.d.cells = (demandH2 (runRowsH t)).cells := by rw [hd]

/-- **`computeChipVCLH_honest_sat_VS` over the memory datum's own cell list.**  The compute side's
serials `idxOf … cells` are positions in `cells := H.d.cells`, the cell list of the memory datum `H`,
and `H.d = demandH2 (runRowsH t)` (`hd`) pins that list to the run's rows (the second conjunct, `rfl`
under `hd`). -/
theorem computeChipVCLH_honest_sat_VS_pinned (H : HonestVCLW (K := K) δF hT hP hC kr)
    (x : ClaimMsgVS) (ρ : Fin 5 → Quad (algebraMap F K δF)) (χ : Coins frameVS K)
    {fuel : ℕ} {subject formula : Noun} {t : NTree (GenComputeRow Kg)} {result : Noun}
    (hrun : genComputeSkeleton (K := Kg) fuel subject formula = .ok (t, result))
    (hd : H.d = demandH2 (runRowsH t))
    (hN : (vsOf H.V).N = (bfsForest [airReorder t]).length)
    (hinj : Function.Injective (vsOf H.V).computeNodes) (hadj : (vsOf H.V).AdjacentC)
    (hcl : HonestClaimMsg H.d.cells (vsOf H.V).claim x)
    (hroot : (rowAtW (bfsForest [airReorder t]) 1).s = (vsOf H.V).claim.subject ∧
      (rowAtW (bfsForest [airReorder t]) 1).f = (vsOf H.V).claim.formula ∧
      (rowAtW (bfsForest [airReorder t]) 1).e = (vsOf H.V).claim.result)
    (hord : (bfsForest [airReorder t]).length ≤ orderOf (χ cAlphaW))
    (hρ3 : Quad.re _ (ρ 3) = accSumX (vsOf H.V).basis H.d.cells (wRows (bfsForest [airReorder t]))
      (chalVH (vsOf H.V).basis χ) (vsOf H.V).N)
    (hρ4 : Quad.re _ (ρ 4) = accSumP (vsOf H.V).basis H.d.cells (wRows (bfsForest [airReorder t]))
      (chalVH (vsOf H.V).basis χ) (vsOf H.V).N)
    (hat : ∀ g ∈ bfsRows (airReorder t),
      AtomsLt (ringChar F) (rowOfSkelH g.skel).sf1 ∧ AtomsLt (ringChar F) (rowOfSkelH g.skel).sf2)
    (hnb : ∀ r < (vsOf H.V).N, NotBadRow (gE (vsOf H.V).basis (baseEnvC H.d.cells (wRows (bfsForest [airReorder t]))
        (bfsForest [airReorder t]).length (chalVH (vsOf H.V).basis χ)
        (pubVH δF (vsOf H.V).basis (vsOf H.V).claim x ρ χ) r))
      (baseEnvC H.d.cells (wRows (bfsForest [airReorder t])) (bfsForest [airReorder t]).length
        (chalVH (vsOf H.V).basis χ) (pubVH δF (vsOf H.V).basis (vsOf H.V).claim x ρ χ) r)) :
    H.d.cells = (demandH2 (runRowsH t)).cells ∧
    RAP.SatisfiesWithPreprocessing
      (ChipH.computeChipVCLH (vsOf H.V).hN (vsOf H.V).computeNodes (vsOf H.V).basis (chalVH (vsOf H.V).basis χ)
        (pubVH δF (vsOf H.V).basis (vsOf H.V).claim x ρ χ) (vsOf H.V).orbitC)
      (compPoly (vsOf H.V).basis H.d.cells (wRows (bfsForest [airReorder t])) (bfsForest [airReorder t]).length
        (chalVH (vsOf H.V).basis χ) (pubVH δF (vsOf H.V).basis (vsOf H.V).claim x ρ χ) (wkLn (χ cAlphaW))
        (wkCnt (bfsForest [airReorder t]) (χ cAlphaW))
        (wkAcc (F := F) (bfsForest [airReorder t]) (χ cAlphaW) (χ cGamW) H.d.cells) (vsOf H.V).computeNodes
        (ChipH.computeChipVCLH (vsOf H.V).hN (vsOf H.V).computeNodes (vsOf H.V).basis (chalVH (vsOf H.V).basis χ)
          (pubVH δF (vsOf H.V).basis (vsOf H.V).claim x ρ χ) (vsOf H.V).orbitC).rap.w) :=
  ⟨pinned_cells H hd, computeChipVCLH_honest_sat_VS (δF := δF) (vsOf H.V) x ρ χ hrun H.d.cells hN hinj hadj
    hcl hroot hord hρ3 hρ4 hat hnb⟩

/-- **The `hcomp` hypothesis of `honest_accepted_VS'`, wired.**  Given that the message's compute trace
polynomials are the honest `compPoly` over the memory datum's own cell list (`hQc`), `hcomp` follows from
the VS satisfaction lemma, with `cells = H.d.cells = (demandH2 (runRowsH t)).cells`. -/
theorem hcomp_pinned {sumC : VerifierData F K hC (shapeVS hT hP) → ClaimMsgVS → SummandsVS (F := F) (K := K) hT hP hC}
    {sumM : VerifierData F K hC (shapeVS hT hP) → Unit → SummandsVS (F := F) (K := K) hT hP hC}
    (H : HonestVCLW (K := K) δF hT hP hC kr)
    (msg : MessagesG (compCoreVS δF hT hP hC sumC) (memCoreVS δF hT hP kr hC sumM)) (χ : Coins frameVS K)
    {fuel : ℕ} {subject formula : Noun} {t : NTree (GenComputeRow Kg)} {result : Noun}
    (hrun : genComputeSkeleton (K := Kg) fuel subject formula = .ok (t, result))
    (hd : H.d = demandH2 (runRowsH t))
    (hN : (vsOf H.V).N = (bfsForest [airReorder t]).length)
    (hinj : Function.Injective (vsOf H.V).computeNodes) (hadj : (vsOf H.V).AdjacentC)
    (hcl : HonestClaimMsg H.d.cells (vsOf H.V).claim msg.msg0C)
    (hroot : (rowAtW (bfsForest [airReorder t]) 1).s = (vsOf H.V).claim.subject ∧
      (rowAtW (bfsForest [airReorder t]) 1).f = (vsOf H.V).claim.formula ∧
      (rowAtW (bfsForest [airReorder t]) 1).e = (vsOf H.V).claim.result)
    (hord : (bfsForest [airReorder t]).length ≤ orderOf (χ cAlphaW))
    (hρ3 : Quad.re _ (msg.requests χ 3) = accSumX (vsOf H.V).basis H.d.cells (wRows (bfsForest [airReorder t]))
      (chalVH (vsOf H.V).basis χ) (vsOf H.V).N)
    (hρ4 : Quad.re _ (msg.requests χ 4) = accSumP (vsOf H.V).basis H.d.cells (wRows (bfsForest [airReorder t]))
      (chalVH (vsOf H.V).basis χ) (vsOf H.V).N)
    (hat : ∀ g ∈ bfsRows (airReorder t),
      AtomsLt (ringChar F) (rowOfSkelH g.skel).sf1 ∧ AtomsLt (ringChar F) (rowOfSkelH g.skel).sf2)
    (hnb : ∀ r < (vsOf H.V).N, NotBadRow (gE (vsOf H.V).basis (baseEnvC H.d.cells (wRows (bfsForest [airReorder t]))
        (bfsForest [airReorder t]).length (chalVH (vsOf H.V).basis χ)
        (pubVH δF (vsOf H.V).basis (vsOf H.V).claim msg.msg0C (msg.requests χ) χ) r))
      (baseEnvC H.d.cells (wRows (bfsForest [airReorder t])) (bfsForest [airReorder t]).length
        (chalVH (vsOf H.V).basis χ) (pubVH δF (vsOf H.V).basis (vsOf H.V).claim msg.msg0C (msg.requests χ) χ) r))
    (hQc : (fun j => msg.Qc χ (Fin.cast rfl j)) =
      compPoly (vsOf H.V).basis H.d.cells (wRows (bfsForest [airReorder t])) (bfsForest [airReorder t]).length
        (chalVH (vsOf H.V).basis χ) (pubVH δF (vsOf H.V).basis (vsOf H.V).claim msg.msg0C (msg.requests χ) χ)
        (wkLn (χ cAlphaW)) (wkCnt (bfsForest [airReorder t]) (χ cAlphaW))
        (wkAcc (F := F) (bfsForest [airReorder t]) (χ cAlphaW) (χ cGamW) H.d.cells) (vsOf H.V).computeNodes
        (ChipH.computeChipVCLH (vsOf H.V).hN (vsOf H.V).computeNodes (vsOf H.V).basis (chalVH (vsOf H.V).basis χ)
          (pubVH δF (vsOf H.V).basis (vsOf H.V).claim msg.msg0C (msg.requests χ) χ) (vsOf H.V).orbitC).rap.w) :
    RAP.SatisfiesWithPreprocessing
      (ChipH.computeChipVCLH (vsOf H.V).hN (vsOf H.V).computeNodes (vsOf H.V).basis (chalVH (vsOf H.V).basis χ)
        (pubVH δF (vsOf H.V).basis (vsOf H.V).claim msg.msg0C (msg.requests χ) χ) (vsOf H.V).orbitC)
      (fun j => msg.Qc χ (Fin.cast rfl j)) := by
  have h := (computeChipVCLH_honest_sat_VS_pinned H msg.msg0C (msg.requests χ) χ hrun hd hN hinj hadj hcl hroot
    hord hρ3 hρ4 hat hnb).2
  rw [← hQc] at h
  exact h

end Pin

end

end Nock.NockVMROM.Thm54.VclL.Handle.FrameVS
