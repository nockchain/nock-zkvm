/-
  Nock/NockVMROM/Thm54/VclL/Handle/HonestAccVSQ.lean

  Additive: a new module.

  * `acceptsG_of_chipsQ`: `AcceptsG` at the VSQ cores from the three chips (the converse of `compute_factsQ`
    / `cell_factsQ` / `walk_factsQ`);
  * `computeChipVCLHQ_honest_sat_VSQ`: `HonestCompQ.computeChipVCLHQ_honest_sat` at `chalVHQ / pubVHQ`;
  * `vsqOf`: the VSQ verifier datum of a `shapeVW` verifier datum (same claim, rows, nodes, orbits);
  * `HonestBadFreeVSQ`: the honest bad events at `frameVSQ` (the 39th's seed / key poles at the old coins,
    the four `𝕂′` twin handle poles);
  * `honest_accepted_VSQ`: the conditional assembly (twin terminals and trace shapes as hypotheses).
-/
import Nock.NockVMROM.Thm54.VclL.Handle.HonestAcceptedVSB
import Nock.NockVMROM.Thm54.VclL.Handle.FrameVSQ
import Nock.NockVMROM.Thm54.VclL.Handle.AcceptVSQ
import Nock.NockVMROM.Thm54.VclL.Handle.HonestCompQ
import Nock.NockVMROM.Thm54.VclL.Handle.HonestTwinQ

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Nock.NockVMROM.Thm54.VclL.Handle.FrameVSQ

open Nock Nock.Noun Nock.Walk Nock.Reified Nock.Framework
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.SVFrame Nock.NockVMROM.Thm54.SVFrameG
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.FrameVS
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.VclL.Compute.LogUp Nock.NockVMROM.Thm54.VclL.Handle.ChipH
open Nock.NockVMROM.Thm54.TraceGen ComputeTable Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.VclL.GenWalk
open Module
open scoped Polynomial

noncomputable section

section Cores
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq F]
  [Fintype K] [DecidableEq K] [Fintype F] (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))]
  [DecidableEq (Quad (algebraMap F K δF))] (hT hP kr hC : ℕ)
variable {sumC : VerifierData F K hC (shapeVSQ hT hP) → ClaimMsgVS → SummandsVSQ (F := F) (K := K) hT hP hC}
  {sumM : VerifierData F K hC (shapeVSQ hT hP) → Unit → SummandsVSQ (F := F) (K := K) hT hP hC}

open Classical in
/-- **`AcceptsG` at the VSQ cores from the three chips** (the converse of `compute_factsQ` / `cell_factsQ` /
`walk_factsQ`). -/
theorem acceptsG_of_chipsQ (V : VerifierData F K hC (shapeVSQ hT hP))
    (msg : MessagesG (compCoreVSQ δF hT hP hC sumC) (memCoreVSQ δF hT hP kr hC sumM)) (χ : Coins frameVSQ K)
    (hGC : GoodCVSQ δF V msg.msg0C (msg.requests χ) χ)
    (hc : RAP.SatisfiesWithPreprocessing
        (ChipHQ.computeChipVCLHQ V.hN V.computeNodes V.basis δF (chalVHQ V.basis χ)
          (pubVHQ δF V.basis V.claim msg.msg0C (msg.requests χ) χ) V.orbitC)
        (fun j => msg.Qc χ (Fin.cast rfl j)))
    (hGM : GoodM V (tCQ hT hP)) (hGW : GoodW V (tWQ hT hP) kr)
    (hcell : ∀ hw : (cellChipHQ δF V.basis (V.hM (tCQ hT hP)) (V.memNodes (tCQ hT hP))
        (V.orbitM (tCQ hT hP)) (chalsVSQ δF χ) (pubsCHQ δF (msg.requests χ) (msg.msg2M χ).1
          (msg.msg2M χ).2)).rap.w = ((shapeVSQ hT hP).table (tCQ hT hP)).width,
      RAP.SatisfiesWithPreprocessing
        (cellChipHQ δF V.basis (V.hM (tCQ hT hP)) (V.memNodes (tCQ hT hP)) (V.orbitM (tCQ hT hP))
          (chalsVSQ δF χ) (pubsCHQ δF (msg.requests χ) (msg.msg2M χ).1 (msg.msg2M χ).2))
        (fun j => msg.Qm χ (tCQ hT hP) (Fin.cast hw j)))
    (hwalk : ∀ hw : (walkChipHQ δF kr V.basis (V.hM (tWQ hT hP)) (V.memNodes (tWQ hT hP))
        (V.orbitM (tWQ hT hP)) (chalsVSQ δF χ) (pubsWHQ δF (msg.requests χ) (msg.msg2M χ).1
          (msg.msg2M χ).2)).rap.w = ((shapeVSQ hT hP).table (tWQ hT hP)).width,
      RAP.SatisfiesWithPreprocessing
        (walkChipHQ δF kr V.basis (V.hM (tWQ hT hP)) (V.memNodes (tWQ hT hP)) (V.orbitM (tWQ hT hP))
          (chalsVSQ δF χ) (pubsWHQ δF (msg.requests χ) (msg.msg2M χ).1 (msg.msg2M χ).2))
        (fun j => msg.Qm χ (tWQ hT hP) (Fin.cast hw j))) :
    AcceptsG V msg χ := by
  refine ⟨?_, fun t => ?_⟩
  · change RAP.SatisfiesWithPreprocessing (chipCVSQ δF V msg.msg0C (msg.requests χ) χ)
      (fun j => msg.Qc χ (Fin.cast (chipCVSQ_width δF V msg.msg0C (msg.requests χ) χ) j))
    have he : chipCVSQ δF V msg.msg0C (msg.requests χ) χ =
        ChipHQ.computeChipVCLHQ V.hN V.computeNodes V.basis δF (chalVHQ V.basis χ)
          (pubVHQ δF V.basis V.claim msg.msg0C (msg.requests χ) χ) V.orbitC := by
      unfold chipCVSQ; exact if_pos hGC
    exact sat_cast_eq he.symm rfl _ _ hc
  · change RAP.SatisfiesWithPreprocessing (chipMVSQ δF hT hP kr V t (msg.requests χ) (msg.msg2M χ) χ)
      (fun j => msg.Qm χ t
        (Fin.cast (chipMVSQ_width δF hT hP kr V t (msg.requests χ) (msg.msg2M χ) χ) j))
    by_cases h0 : (t : ℕ) = 0
    · obtain rfl : t = tCQ hT hP := Fin.ext h0
      have he : chipMVSQ δF hT hP kr V (tCQ hT hP) (msg.requests χ) (msg.msg2M χ) χ =
          cellChipHQ δF V.basis (V.hM (tCQ hT hP)) (V.memNodes (tCQ hT hP)) (V.orbitM (tCQ hT hP))
            (chalsVSQ δF χ) (pubsCHQ δF (msg.requests χ) (msg.msg2M χ).1 (msg.msg2M χ).2) := by
        unfold chipMVSQ; rw [if_pos h0, if_pos hGM]
      have hw : (cellChipHQ δF V.basis (V.hM (tCQ hT hP)) (V.memNodes (tCQ hT hP))
          (V.orbitM (tCQ hT hP)) (chalsVSQ δF χ) (pubsCHQ δF (msg.requests χ) (msg.msg2M χ).1
            (msg.msg2M χ).2)).rap.w = ((shapeVSQ hT hP).table (tCQ hT hP)).width := by
        rw [← he]; exact chipMVSQ_width δF hT hP kr V _ _ _ _
      exact sat_cast_eq he.symm hw _ _ (hcell hw)
    · have ht1 : t = tWQ hT hP := Fin.ext (by have h2 : (t : ℕ) < 2 := t.2; show (t : ℕ) = 1; omega)
      subst ht1
      have h1 : ¬ ((tWQ hT hP : Fin (shapeVSQ hT hP).k) : ℕ) = 0 := Nat.one_ne_zero
      have he : chipMVSQ δF hT hP kr V (tWQ hT hP) (msg.requests χ) (msg.msg2M χ) χ =
          walkChipHQ δF kr V.basis (V.hM (tWQ hT hP)) (V.memNodes (tWQ hT hP)) (V.orbitM (tWQ hT hP))
            (chalsVSQ δF χ) (pubsWHQ δF (msg.requests χ) (msg.msg2M χ).1 (msg.msg2M χ).2) := by
        unfold chipMVSQ; rw [if_neg h1, if_pos hGW]
      have hw : (walkChipHQ δF kr V.basis (V.hM (tWQ hT hP)) (V.memNodes (tWQ hT hP))
          (V.orbitM (tWQ hT hP)) (chalsVSQ δF χ) (pubsWHQ δF (msg.requests χ) (msg.msg2M χ).1
            (msg.msg2M χ).2)).rap.w = ((shapeVSQ hT hP).table (tWQ hT hP)).width := by
        rw [← he]; exact chipMVSQ_width δF hT hP kr V _ _ _ _
      exact sat_cast_eq he.symm hw _ _ (hwalk hw)

end Cores

section CompQ
variable {F K Kg : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq F] [Fintype K]
  [Field Kg] (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))] {hC : ℕ} {S : MemShape}

theorem limbVal_congr_lt (b : Basis (Fin 3) F K) (f g : ℕ → F) (c0 n : ℕ) (hc : c0 + 2 < n)
    (h : ∀ j < n, f j = g j) : limbVal b f c0 = limbVal b g c0 := by
  unfold limbVal
  refine Finset.sum_congr rfl fun k _ => ?_
  have hk := k.isLt
  rw [h (c0 + k) (by omega)]

/-- **`computeChipVCLH_honest_sat_VS` at the `𝕂′` frame**: the compute chip `computeChipVCLHQ` accepts
`compPolyQ` over the claim's cell list, at `chalVHQ / pubVHQ`.  The `𝕂′` terminals `ρ₃ / ρ₄` are the
honest `𝕂′` totals `accSumXQ / accSumPQ`; `hnb` is the priced `𝕂′` pole event. -/
theorem computeChipVCLHQ_honest_sat_VSQ (V : VerifierData F K hC S) (x : ClaimMsgVS)
    (ρ : Fin 5 → Quad (algebraMap F K δF)) (χ : Coins frameVSQ K)
    {fuel : ℕ} {subject formula : Noun} {t : NTree (GenComputeRow Kg)} {result : Noun}
    (hrun : genComputeSkeleton (K := Kg) fuel subject formula = .ok (t, result)) (cells : List Noun)
    (hN : V.N = (bfsForest [airReorder t]).length)
    (hinj : Function.Injective V.computeNodes) (hadj : V.AdjacentC)
    (hcl : HonestClaimMsg cells V.claim x)
    (hroot : (rowAtW (bfsForest [airReorder t]) 1).s = V.claim.subject ∧
      (rowAtW (bfsForest [airReorder t]) 1).f = V.claim.formula ∧
      (rowAtW (bfsForest [airReorder t]) 1).e = V.claim.result)
    (hord : (bfsForest [airReorder t]).length ≤ orderOf ((toVS χ) cAlphaW))
    (hρ3 : ρ 3 = HonestCompQ.accSumXQ δF V.basis cells (wRows (bfsForest [airReorder t]))
      (chalVHQ V.basis χ) V.N)
    (hρ4 : ρ 4 = HonestCompQ.accSumPQ δF V.basis cells (wRows (bfsForest [airReorder t]))
      (chalVHQ V.basis χ) V.N)
    (hat : ∀ g ∈ bfsRows (airReorder t),
      AtomsLt (ringChar F) (rowOfSkelH g.skel).sf1 ∧ AtomsLt (ringChar F) (rowOfSkelH g.skel).sf2)
    (hnb : ∀ r < V.N, NotBadRow (HonestCompQ.eCQ δF V.basis (chalVHQ V.basis χ))
      (baseEnvC cells (wRows (bfsForest [airReorder t])) (bfsForest [airReorder t]).length
        (chalVHQ V.basis χ) (pubVHQ δF V.basis V.claim x ρ χ) r)) :
    RAP.SatisfiesWithPreprocessing
      (ChipHQ.computeChipVCLHQ V.hN V.computeNodes V.basis δF (chalVHQ V.basis χ)
        (pubVHQ δF V.basis V.claim x ρ χ) V.orbitC)
      (HonestCompQ.compPolyQ δF V.basis cells (wRows (bfsForest [airReorder t]))
        (bfsForest [airReorder t]).length (chalVHQ V.basis χ) (pubVHQ δF V.basis V.claim x ρ χ)
        (wkLn ((toVS χ) cAlphaW)) (wkCnt (bfsForest [airReorder t]) ((toVS χ) cAlphaW))
        (wkAcc (F := F) (bfsForest [airReorder t]) ((toVS χ) cAlphaW) ((toVS χ) cGamW) cells) V.computeNodes
        (ChipHQ.computeChipVCLHQ V.hN V.computeNodes V.basis δF (chalVHQ V.basis χ)
          (pubVHQ δF V.basis V.claim x ρ χ) V.orbitC).rap.w) := by
  have hW : 0 < (bfsForest [airReorder t]).length := by rw [← hN]; exact V.hN
  have hcv : ∀ j < 12, chalVHQ V.basis χ j = chalVH V.basis (toVS χ) j := fun j hj => chalVHQ_old V.basis χ j hj
  have hpv : ∀ j < 21, pubVHQ δF V.basis V.claim x ρ χ j = pubVH δF V.basis V.claim x ρ (toVS χ) j := fun j hj => by
    simp only [pubVHQ, if_pos hj]
  refine HonestCompQ.computeChipVCLHQ_honest_sat δF hrun cells ((toVS χ) cAlphaW) ((toVS χ) cGamW) hord V.hN hN
    V.computeNodes hinj V.basis (chalVHQ V.basis χ) (pubVHQ δF V.basis V.claim x ρ χ) V.orbitC hadj
    ((limbVal_congr_lt V.basis _ _ chalAlphaW 12 (by decide) hcv).trans (limb_chal_alpha V.basis (toVS χ)))
    ((limbVal_congr_lt V.basis _ _ chalGammaW 12 (by decide) hcv).trans (limb_chal_gamma V.basis (toVS χ)))
    ((limbVal_congr_lt V.basis _ _ pubIC 21 (by decide) hpv).trans (limb_pubVH_IC δF V.basis (toVS χ) V.claim x ρ))
    ((limbVal_congr_lt V.basis _ _ pubSeed 21 (by decide) hpv).trans
      ((limb_pubVH_seed δF V.basis (toVS χ) V.claim x ρ).trans (seedVS_eq_wkSeed cells V.claim x hcl (toVS χ) _ hW hroot)))
    ((limbVal_congr_lt V.basis _ _ pubOut 21 (by decide) hpv).trans (limb_pubVH_out δF V.basis (toVS χ) V.claim x ρ))
    (fun i hi => (hpv i (by omega)).trans (pubVH_lt6_eq_pubVec δF cells V.claim x hcl V.basis ρ (toVS χ) _ hroot i hi))
    (fun k => by
      rw [hpv _ (by simp [pubRhoX]; omega), pubVH_rhoX, hρ3])
    (fun k => by
      have hk := k.isLt
      simp only [pubVHQ, ChipHQ.pubRhoXIm]
      erw [if_neg (by omega), dif_pos (by omega)]
      rw [hρ3]; congr 1; apply Fin.ext; simp)
    (fun k => by
      rw [hpv _ (by simp [pubRhoP]; omega), pubVH_rhoP, hρ4])
    (fun k => by
      have hk := k.isLt
      simp only [pubVHQ, ChipHQ.pubRhoPIm]
      erw [if_neg (by omega), dif_neg (by omega), dif_pos (by omega)]
      rw [hρ4]; congr 1; apply Fin.ext; simp)
    hat (fun r hr => hnb r hr)

end CompQ

section VsqOf
variable {F K : Type} [Field F] [Field K] [Algebra F K] {hT hP hC : ℕ}

theorem height_eq_VSQ (t : Fin 2) :
    ((shapeVSQ hT hP).table t).height = ((shapeVW hT hP).table t).height := by
  simp only [shapeVSQ, shapeVW, shapeVCL]; split_ifs <;> rfl

/-- **The VSQ verifier data of an honest `shapeVW` verifier data**: the same claim, rows, nodes and orbits. -/
def vsqOf (V : VerifierData F K hC (shapeVW hT hP)) : VerifierData F K hC (shapeVSQ hT hP) :=
  ⟨V.claim, V.N, V.hN, V.Ksz, V.basis, V.orbitC, V.computeNodes, V.memRows, V.hM,
    fun t => (height_eq_VSQ (hT := hT) (hP := hP) t).symm ▸ V.orbitM t, V.memNodes⟩

end VsqOf

section Accepted
variable {F K Kg : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq F]
  [Fintype K] [DecidableEq K] [Fintype F] [Fact (ringChar F).Prime] [Algebra (ZMod (ringChar F)) K]
  [Field Kg] {δF : F} [Fact (¬ IsSquare (algebraMap F K δF))] [DecidableEq (Quad (algebraMap F K δF))]
  {hT hP hC kr : ℕ} (H : HonestVCLW (K := K) δF hT hP hC kr)

/-- **The honest bad events NOT occurring, at the `𝕂′` frame.**  The seed and key-pole events at the old
coins (as `HonestBadFreeVSB`); the twin denominators at the `𝕂′` handle coins (`hpoleC`, `hpoleX/L/R`,
one pole coin per row-record, priced at `1/|𝕂′|`). -/
structure HonestBadFreeVSQ (bs : List Noun) (χ : Coins frameVSQ K)
    (ρ : Fin 5 → Quad (algebraMap F K δF)) (y yH : Quad (algebraMap F K δF))
    (mhv : Fin (H.V.memRows (tCW hT hP)) → F)
    (kLv vLv kRv vRv : Fin (H.V.memRows (tWW hT hP)) → F) : Prop where
  hz : zC (δF := δF) (toVCL (toVS χ)) ≠ 0
  h0 : ∀ v ∈ H.keys0 (toVCL (toVS χ)),
    FiniteIO.compress (m := 5) ⟨γC (toVCL (toVS χ)), ρC (toVCL (toVS χ))⟩ v ≠ 0
  h1 : ∀ v ∈ H.keys1 (toVCL (toVS χ)),
    FiniteIO.compress (m := 11) ⟨γC (toVCL (toVS χ)), ρC (toVCL (toVS χ))⟩ v ≠ 0
  h2 : ∀ v ∈ H.keys2 (toVCL (toVS χ)),
    FiniteIO.compress (m := 8) ⟨γC (toVCL (toVS χ)), ρC (toVCL (toVS χ))⟩ v ≠ 0
  hpoleC : ∀ i, CellTraceHQ.dRow δF H.V.basis (H.V.hM (tCW hT hP)) (H.V.memNodes (tCW hT hP))
      (H.V.orbitM (tCW hT hP)) (chalsVSQ δF χ) (pubsCHQ δF ρ y yH)
      (cellColB H bs (toVCL (toVS χ))) mhv i ≠ 0
  hpoleX : ∀ i, WalkTraceHQ.dRow δF kr H.V.basis (H.V.hM (tWW hT hP)) (H.V.memNodes (tWW hT hP))
      (H.V.orbitM (tWW hT hP)) (chalsVSQ δF χ) (pubsWHQ δF ρ y yH) WalkHC.xKeyH (walkColVS H (toVS χ))
      kLv vLv kRv vRv i ≠ 0
  hpoleL : ∀ i, WalkTraceHQ.dRow δF kr H.V.basis (H.V.hM (tWW hT hP)) (H.V.memNodes (tWW hT hP))
      (H.V.orbitM (tWW hT hP)) (chalsVSQ δF χ) (pubsWHQ δF ρ y yH) WalkHC.recLH (walkColVS H (toVS χ))
      kLv vLv kRv vRv i ≠ 0
  hpoleR : ∀ i, WalkTraceHQ.dRow δF kr H.V.basis (H.V.hM (tWW hT hP)) (H.V.memNodes (tWW hT hP))
      (H.V.orbitM (tWW hT hP)) (chalsVSQ δF χ) (pubsWHQ δF ρ y yH) WalkHC.recRH (walkColVS H (toVS χ))
      kLv vLv kRv vRv i ≠ 0


open Classical in
/-- **The honest VSQ assembly** (the `𝕂′` twin of `honest_accepted_VS'`).  Outside the honest bad events
(`HonestBadFreeVSQ`: seed / key poles at the old coins, the `𝕂′` handle poles), the VSQ messages whose
compute trace is `compPolyQ` and whose memory traces are `cellTraceHQ` / `walkTraceHQ` over the 39th's honest
columns satisfy `AcceptsG` at `frameVSQ`.  Compute: `computeChipVCLHQ_honest_sat_VSQ`; memory:
`cellTwinQ_accepted` / `walkTwinQ_accepted` over `cell_acceptedW_genB` / `walk_acceptedW_gen`. -/
theorem honest_accepted_VSQ
    {sumC : VerifierData F K hC (shapeVSQ hT hP) → ClaimMsgVS → SummandsVSQ (F := F) (K := K) hT hP hC}
    {sumM : VerifierData F K hC (shapeVSQ hT hP) → Unit → SummandsVSQ (F := F) (K := K) hT hP hC}
    (msg : MessagesG (compCoreVSQ δF hT hP hC sumC) (memCoreVSQ δF hT hP kr hC sumM)) (χ : Coins frameVSQ K)
    (ρ : Fin 5 → Quad (algebraMap F K δF)) (y yH : Quad (algebraMap F K δF))
    (mhv : Fin (H.V.memRows (tCW hT hP)) → F)
    (kLv vLv kRv vRv : Fin (H.V.memRows (tWW hT hP)) → F)
    (hρ : msg.requests χ = ρ) (hy : msg.msg2M χ = (y, yH))
    (hQC : ∀ j : Fin 238, msg.Qm χ (tCQ hT hP) j = CellTraceHQ.cellTraceHQ δF H.V.basis
      (H.V.hM (tCW hT hP)) (H.V.memNodes (tCW hT hP)) (H.V.orbitM (tCW hT hP)) (chalsVSQ δF χ)
      (pubsCHQ δF ρ y yH) (cellColB H (claimBinds H.V.claim) (toVCL (toVS χ))) mhv j)
    (hQW : ∀ j : Fin 166, msg.Qm χ (tWQ hT hP) j = WalkTraceHQ.walkTraceHQ δF kr H.V.basis
      (H.V.hM (tWW hT hP)) (H.V.memNodes (tWW hT hP)) (H.V.orbitM (tWW hT hP)) (chalsVSQ δF χ)
      (pubsWHQ δF ρ y yH) (walkColVS H (toVS χ)) kLv vLv kRv vRv j)
    (hbf : HonestBadFreeVSQ H (claimBinds H.V.claim) χ ρ y yH mhv kLv vLv kRv vRv)
    (hρ0 : rho3 δF ρ 0 = vTotB H (claimBinds H.V.claim) (toVCL (toVS χ)))
    (hρ1 : rho3 δF ρ 1 + y = H.xTot (toVCL (toVS χ))) (hyT : y = H.yTot (toVCL (toVS χ)))
    (hρ2 : rho3 δF ρ 2 = H.pTot (toVCL (toVS χ)))
    (hkL : ∀ i, kLv i = 0 ∨ kLv i = 1) (hkR : ∀ i, kRv i = 0 ∨ kRv i = 1)
    (hpubC : ρ 3 + yH = ∑ j ∈ Finset.range (H.V.memRows (tCW hT hP)),
      liftQ δF (CellTraceH.mN mhv j) * (CellTraceHQ.dN δF H.V.basis (H.V.hM (tCW hT hP))
        (H.V.memNodes (tCW hT hP)) (H.V.orbitM (tCW hT hP)) (chalsVSQ δF χ) (pubsCHQ δF ρ y yH)
        (cellColB H (claimBinds H.V.claim) (toVCL (toVS χ))) mhv j)⁻¹)
    (hpubX : yH = ∑ j ∈ Finset.range (H.V.memRows (tWW hT hP)),
      (WalkTraceHQ.dN δF kr H.V.basis (H.V.hM (tWW hT hP)) (H.V.memNodes (tWW hT hP))
        (H.V.orbitM (tWW hT hP)) (chalsVSQ δF χ) (pubsWHQ δF ρ y yH) (walkColVS H (toVS χ))
        kLv vLv kRv vRv WalkHC.xKeyH j)⁻¹)
    (hpubP : ρ 4 = ∑ j ∈ Finset.range (H.V.memRows (tWW hT hP)),
      (liftQ δF (WalkTraceH.cN j (walkColVS H (toVS χ) WChip.mL)) *
          (WalkTraceHQ.dN δF kr H.V.basis (H.V.hM (tWW hT hP)) (H.V.memNodes (tWW hT hP))
            (H.V.orbitM (tWW hT hP)) (chalsVSQ δF χ) (pubsWHQ δF ρ y yH) (walkColVS H (toVS χ))
            kLv vLv kRv vRv WalkHC.recLH j)⁻¹ +
        liftQ δF (WalkTraceH.cN j (walkColVS H (toVS χ) WChip.mR)) *
          (WalkTraceHQ.dN δF kr H.V.basis (H.V.hM (tWW hT hP)) (H.V.memNodes (tWW hT hP))
            (H.V.orbitM (tWW hT hP)) (chalsVSQ δF χ) (pubsWHQ δF ρ y yH) (walkColVS H (toVS χ))
            kLv vLv kRv vRv WalkHC.recRH j)⁻¹))
    (hslot : ∀ r ∈ pathReads H.d.preads, (Noun.slot r.2 r.1).isSome) (hreads : H.d.reads = [])
    (hadj : (vsOf H.V).AdjacentC) (hinj : Function.Injective (vsOf H.V).computeNodes)
    (hbs : ∀ b ∈ (claimBinds H.V.claim).flatMap selfCell, b ∈ H.d.cells)
    (hm : HonestClaimMsgFull H.d.cells H.V.claim msg.msg0C)
    {fuel : ℕ} {subject formula : Noun} {t : NTree (GenComputeRow Kg)} {result : Noun}
    (hrun : genComputeSkeleton (K := Kg) fuel subject formula = .ok (t, result))
    (hN : (vsqOf H.V).N = (bfsForest [airReorder t]).length)
    (hroot : (rowAtW (bfsForest [airReorder t]) 1).s = H.V.claim.subject ∧
      (rowAtW (bfsForest [airReorder t]) 1).f = H.V.claim.formula ∧
      (rowAtW (bfsForest [airReorder t]) 1).e = H.V.claim.result)
    (hord : (bfsForest [airReorder t]).length ≤ orderOf ((toVS χ) cAlphaW))
    (hρ3 : ρ 3 = HonestCompQ.accSumXQ δF H.V.basis H.d.cells (wRows (bfsForest [airReorder t]))
      (chalVHQ H.V.basis χ) (vsqOf H.V).N)
    (hρ4 : ρ 4 = HonestCompQ.accSumPQ δF H.V.basis H.d.cells (wRows (bfsForest [airReorder t]))
      (chalVHQ H.V.basis χ) (vsqOf H.V).N)
    (hat : ∀ g ∈ bfsRows (airReorder t),
      AtomsLt (ringChar F) (rowOfSkelH g.skel).sf1 ∧ AtomsLt (ringChar F) (rowOfSkelH g.skel).sf2)
    (hnb : ∀ r < (vsqOf H.V).N, NotBadRow (HonestCompQ.eCQ δF H.V.basis (chalVHQ H.V.basis χ))
      (baseEnvC H.d.cells (wRows (bfsForest [airReorder t])) (bfsForest [airReorder t]).length
        (chalVHQ H.V.basis χ) (pubVHQ δF H.V.basis H.V.claim msg.msg0C (msg.requests χ) χ) r))
    (hQc : (fun j => msg.Qc χ (Fin.cast rfl j)) =
      HonestCompQ.compPolyQ δF H.V.basis H.d.cells (wRows (bfsForest [airReorder t]))
        (bfsForest [airReorder t]).length (chalVHQ H.V.basis χ)
        (pubVHQ δF H.V.basis H.V.claim msg.msg0C (msg.requests χ) χ)
        (wkLn ((toVS χ) cAlphaW)) (wkCnt (bfsForest [airReorder t]) ((toVS χ) cAlphaW))
        (wkAcc (F := F) (bfsForest [airReorder t]) ((toVS χ) cAlphaW) ((toVS χ) cGamW) H.d.cells)
        (vsqOf H.V).computeNodes
        (ChipHQ.computeChipVCLHQ (vsqOf H.V).hN (vsqOf H.V).computeNodes (vsqOf H.V).basis δF
          (chalVHQ (vsqOf H.V).basis χ)
          (pubVHQ δF (vsqOf H.V).basis (vsqOf H.V).claim msg.msg0C (msg.requests χ) χ)
          (vsqOf H.V).orbitC).rap.w) :
    AcceptsG (vsqOf H.V) msg χ := by
  have hy1 : y = (msg.msg2M χ).1 := by rw [hy]
  have hy2 : yH = (msg.msg2M χ).2 := by rw [hy]
  subst hρ hy1 hy2
  have hcl : HonestClaimMsg H.d.cells H.V.claim msg.msg0C := fun k hk => by rw [hm k hk]
  have hGC : GoodCVSQ δF (vsqOf H.V) msg.msg0C (msg.requests χ) χ := by
    refine ⟨hadj, hinj, H.hq, ?_, ?_⟩
    · exact hρ0.trans (vTotB_eq_claimValSum H hbs msg.msg0C hm (toVS χ))
    · have h := H.xTot_sub_yTot_eq (toVCL (toVS χ)) hslot
      rw [hreads] at h
      have : rho3 δF (msg.requests χ) 1 = H.xTot (toVCL (toVS χ)) - H.yTot (toVCL (toVS χ)) := by
        rw [← hyT]; exact eq_sub_of_add_eq hρ1
      exact this.trans (h.trans (by simp [shallowSided, shallowReads]))
  have hcompQ := computeChipVCLHQ_honest_sat_VSQ δF (vsqOf H.V) msg.msg0C (msg.requests χ) χ hrun H.d.cells hN hinj
    hadj hcl hroot hord hρ3 hρ4 hat hnb
  have hcompQ' : RAP.SatisfiesWithPreprocessing
      (ChipHQ.computeChipVCLHQ (vsqOf H.V).hN (vsqOf H.V).computeNodes (vsqOf H.V).basis δF
        (chalVHQ (vsqOf H.V).basis χ)
        (pubVHQ δF (vsqOf H.V).basis (vsqOf H.V).claim msg.msg0C (msg.requests χ) χ) (vsqOf H.V).orbitC)
      (fun j => msg.Qc χ (Fin.cast rfl j)) := by
    exact (congrArg (RAP.SatisfiesWithPreprocessing _) hQc).mpr hcompQ
  have hch : ∀ j < 33, chalsVSQ δF χ j = chalsVCL δF (toVCL (toVS χ)) j := fun j hj => by
    have := chalsVS_old δF (toVS χ) j hj
    simp only [chalsVSQ]
    rw [if_neg (by omega), if_neg (by omega)]
    exact this
  have hpC : ∀ i < 4, pubsCHQ δF (msg.requests χ) (msg.msg2M χ).1 (msg.msg2M χ).2 i =
      pubsC δF (rho3 δF (msg.requests χ)) (msg.msg2M χ).1 i := fun i hi => by
    simp only [pubsCHQ]; rw [if_neg (by omega), if_neg (by omega)]
  have hpW : ∀ i < 4, pubsWHQ δF (msg.requests χ) (msg.msg2M χ).1 (msg.msg2M χ).2 i =
      pubsP δF (rho3 δF (msg.requests χ)) (msg.msg2M χ).1 i := fun i hi => by
    simp only [pubsWHQ]; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  have hcell := cellTwinQ_accepted δF H.V.basis (H.V.hM (tCW hT hP)) (H.V.memNodes (tCW hT hP))
    (H.V.orbitM (tCW hT hP)) (chalsVSQ δF χ) (pubsCHQ δF (msg.requests χ) (msg.msg2M χ).1 (msg.msg2M χ).2)
    _ mhv (H.hinj _) (H.hadj _)
    (cell_acceptedW_genB H (claimBinds H.V.claim) (toVCL (toVS χ)) (chalsVSQ δF χ)
      (pubsCHQ δF (msg.requests χ) (msg.msg2M χ).1 (msg.msg2M χ).2) hch (rho3 δF (msg.requests χ))
      (msg.msg2M χ).1 hpC hbf.hz hbf.h0 hbf.h1 hρ0 hρ1)
    hbf.hpoleC (by
      have e : Quad.mk _ (pubsCHQ δF (msg.requests χ) (msg.msg2M χ).1 (msg.msg2M χ).2 CellHQ.pubHQ)
          (pubsCHQ δF (msg.requests χ) (msg.msg2M χ).1 (msg.msg2M χ).2 (CellHQ.pubHQ + 1)) =
          (msg.requests χ) 3 + (msg.msg2M χ).2 := by
        simp [pubsCHQ, CellHQ.pubHQ, Quad.mk_re_im]
      rw [e]; exact hpubC)
  have hwalk := walkTwinQ_accepted δF kr H.V.basis (H.V.hM (tWW hT hP)) (H.V.memNodes (tWW hT hP))
    (H.V.orbitM (tWW hT hP)) (chalsVSQ δF χ) (pubsWHQ δF (msg.requests χ) (msg.msg2M χ).1 (msg.msg2M χ).2)
    _ kLv vLv kRv vRv (H.hinj _) (H.hadj _)
    (walk_acceptedW_gen H (toVCL (toVS χ)) (chalsVSQ δF χ)
      (pubsWHQ δF (msg.requests χ) (msg.msg2M χ).1 (msg.msg2M χ).2) hch (rho3 δF (msg.requests χ))
      (msg.msg2M χ).1 hpW hbf.h1 hbf.h2 hyT hρ2)
    hkL hkR hbf.hpoleX hbf.hpoleL hbf.hpoleR (by
      have e : Quad.mk _ (pubsWHQ δF (msg.requests χ) (msg.msg2M χ).1 (msg.msg2M χ).2 WalkHQ.pubXQ)
          (pubsWHQ δF (msg.requests χ) (msg.msg2M χ).1 (msg.msg2M χ).2 (WalkHQ.pubXQ + 1)) =
          (msg.msg2M χ).2 := by
        simp [pubsWHQ, WalkHQ.pubXQ, Quad.mk_re_im]
      rw [e]; exact hpubX) (by
      have e : Quad.mk _ (pubsWHQ δF (msg.requests χ) (msg.msg2M χ).1 (msg.msg2M χ).2 WalkHQ.pubPQ)
          (pubsWHQ δF (msg.requests χ) (msg.msg2M χ).1 (msg.msg2M χ).2 (WalkHQ.pubPQ + 1)) =
          (msg.requests χ) 4 := by
        simp [pubsWHQ, WalkHQ.pubPQ, Quad.mk_re_im]
      rw [e]; exact hpubP)
  refine acceptsG_of_chipsQ δF hT hP kr hC (vsqOf H.V) msg χ hGC hcompQ' (goodM_vsOf_C H) (goodW_vsOf H)
    (fun hw => ?_) (fun hw => ?_)
  · have hfun : (fun j => msg.Qm χ (tCQ hT hP) (Fin.cast hw j)) = fun j => CellTraceHQ.cellTraceHQ δF H.V.basis
        (H.V.hM (tCW hT hP)) (H.V.memNodes (tCW hT hP)) (H.V.orbitM (tCW hT hP)) (chalsVSQ δF χ)
        (pubsCHQ δF (msg.requests χ) (msg.msg2M χ).1 (msg.msg2M χ).2)
        (cellColB H (claimBinds H.V.claim) (toVCL (toVS χ))) mhv
        (Fin.cast (cellChipHQ_width δF H.V.basis (H.V.hM (tCW hT hP)) (H.V.memNodes (tCW hT hP))
          (H.V.orbitM (tCW hT hP)) (chalsVSQ δF χ)
          (pubsCHQ δF (msg.requests χ) (msg.msg2M χ).1 (msg.msg2M χ).2)) j) :=
      funext fun j => hQC _
    rw [hfun]; exact hcell
  · have hfun : (fun j => msg.Qm χ (tWQ hT hP) (Fin.cast hw j)) = fun j => WalkTraceHQ.walkTraceHQ δF kr H.V.basis
        (H.V.hM (tWW hT hP)) (H.V.memNodes (tWW hT hP)) (H.V.orbitM (tWW hT hP)) (chalsVSQ δF χ)
        (pubsWHQ δF (msg.requests χ) (msg.msg2M χ).1 (msg.msg2M χ).2) (walkColVS H (toVS χ)) kLv vLv kRv vRv
        (Fin.cast (walkChipHQ_width δF kr H.V.basis (H.V.hM (tWW hT hP)) (H.V.memNodes (tWW hT hP))
          (H.V.orbitM (tWW hT hP)) (chalsVSQ δF χ)
          (pubsWHQ δF (msg.requests χ) (msg.msg2M χ).1 (msg.msg2M χ).2)) j) :=
      funext fun j => hQW _
    rw [hfun]; exact hwalk

end Accepted

end

end Nock.NockVMROM.Thm54.VclL.Handle.FrameVSQ
