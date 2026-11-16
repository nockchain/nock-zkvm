/-
  Nock/NockVMROM/Thm54/VclL/Handle/HonestClaimH.lean

* §1 `HonestClaimMsg` (the honest claim message: each cell claim noun carries its closure serial),
    `labelF_eq_hl`, `limb_chalVH`, `limb_pubVH_*`, `pubVH_rho*`, `seedVS_eq_wkSeed`, `pubVH_lt6_eq_pubVec`: every reading
    hypothesis of `computeChipVCLH_honest_sat` is a definitional / honest-message fact at `chalVH` / `pubVH`.
  * §2 `computeChipVCLH_honest_sat_VS`: `hcomp` of `honest_accepted_VS` at the VS verifier data, from the honest
    compute trace polynomials; remaining hypotheses: `hord`, `hat`, the priced pole event `hnb`, and the compute
    terminals `hρ3 / hρ4` (`Re ρ₃ / Re ρ₄` = the compute's export / path totals).
  * §3 FINDING `HonestVCLW.vTot_eq_zero` / `honest_VS_hyps_force_claimValSum_zero`: the 39th's honest memory datum
    has `binds = []` (`vcsOf cells []`), so its validity total is `0` (`cell_vTotal`), while `GoodCVS` pins
    `ρ 0 = claimValSum`.  The hypotheses `hρ0` and `hGC` of `honest_accepted_VS` are therefore jointly satisfiable
    only if `claimValSum = 0`; a claim with a cell noun needs an honest datum with `binds` = the claim cells.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.HonestCompSatH
import Nock.NockVMROM.Thm54.VclL.Handle.HonestAcceptedVS
import Nock.NockVMROM.Thm54.VclL.Chips.HonestMemReq

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000

namespace Nock.NockVMROM.Thm54.VclL.Handle.FrameVS

open Nock Nock.Noun Nock.Walk Nock.Reified Nock.Framework Module
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.SVFrame Nock.NockVMROM.Thm54.SVFrameG
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Compute.LogUp
open Nock.NockVMROM.Thm54.VclL.Handle.ChipH
open Nock.NockVMROM.Thm54.TraceGen ComputeTable Nock.NockVMROM.Thm54.SemanticStrategy
open scoped Polynomial

noncomputable section

section Claim
variable {F K : Type} [Field F] [Field K] [Algebra F K] [Fintype K] [FiniteDimensional F K] [DecidableEq F]
  (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))]

/-- The honest claim message: every cell claim noun is handled by its serial `idxOf` in the cell list. -/
def HonestClaimMsg (cells : List Noun) (c : P8PublicClaim) (m : ClaimMsgVS) : Prop :=
  ∀ k : Fin 3, (claimNoun c k).isCell = true → (m k).1 = cells.idxOf (claimNoun c k)

theorem claimH_eq_hdl (cells : List Noun) (c : P8PublicClaim) (m : ClaimMsgVS)
    (hm : HonestClaimMsg cells c m) (k : Fin 3) :
    hvalF (F := F) (claimH c m k) = [(hdl cells (claimNoun c k) : F × F).1, (hdl cells (claimNoun c k) : F × F).2] := by
  unfold claimH
  generalize hx : claimNoun c k = x
  cases x with
  | atom v => simp [claimHandle, hvalF, hdl]
  | cell a b =>
    have := hm k (by rw [hx]; rfl)
    rw [hx] at this
    simp [claimHandle, hvalF, hdl, this]

theorem labelF_eq_hl (cells : List Noun) (c : P8PublicClaim) (m : ClaimMsgVS)
    (hm : HonestClaimMsg cells c m) :
    labelF (F := F) c m = hl cells (c.subject, c.formula, c.result) := by
  have h0 := claimH_eq_hdl (F := F) cells c m hm 0
  have h1 := claimH_eq_hdl (F := F) cells c m hm 1
  have h2 := claimH_eq_hdl (F := F) cells c m hm 2
  simp only [claimNoun, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at h0 h1 h2
  simp only [labelF, h0, h1, h2, hl]
  simp [claimNoun]

end Claim

section Coins
variable {F K : Type} [Field F] [Field K] [Algebra F K] [Fintype K] [FiniteDimensional F K] [DecidableEq F]
  (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))]
variable (b : Basis (Fin 3) F K) (χ : Coins frameVS K)

theorem limb_chalVH (q : ℕ) (hq : q < 4) :
    limbVal b (chalVH b χ) (3 * q) = coinH χ q := by
  refine limbVal_eq_of_coords b _ _ _ fun k => ?_
  have hk := k.isLt
  simp only [chalVH]
  rw [if_pos (by omega)]
  have e1 : (3 * q + (k : ℕ)) / 3 = q := by omega
  congr 1
  · rw [e1]
  · apply Fin.ext; simp; omega

theorem limb_chal_alpha : limbVal b (chalVH b χ) chalAlphaW = χ cAlphaW := by
  have := limb_chalVH b χ 2 (by omega)
  simpa [coinH, chalAlphaW] using this

theorem limb_chal_gamma : limbVal b (chalVH b χ) chalGammaW = χ cGamW := by
  have := limb_chalVH b χ 3 (by omega)
  simpa [coinH, chalGammaW] using this

variable (c : P8PublicClaim) (m : ClaimMsgVS) (ρ : Fin 5 → Quad (algebraMap F K δF))

theorem limb_pubVH_IC : limbVal b (pubVH δF b c m ρ χ) pubIC = χ cAlphaW := by
  refine limbVal_eq_of_coords b _ _ _ fun k => ?_
  have hk := k.isLt
  simp only [pubVH, pubIC]
  erw [if_neg (by omega), dif_pos (by omega)]
  congr 1; apply Fin.ext; simp

theorem limb_pubVH_seed : limbVal b (pubVH δF b c m ρ χ) pubSeed = seedVS (F := F) c m χ := by
  refine limbVal_eq_of_coords b _ _ _ fun k => ?_
  have hk := k.isLt
  simp only [pubVH, pubSeed]
  erw [if_neg (by omega), dif_neg (by omega), dif_pos (by omega)]
  congr 1; apply Fin.ext; simp

theorem limb_pubVH_out : limbVal b (pubVH δF b c m ρ χ) pubOut = 0 := by
  refine limbVal_eq_of_coords b _ _ _ fun k => ?_
  have hk := k.isLt
  simp only [pubVH, pubOut]
  erw [if_neg (by omega), dif_neg (by omega), dif_neg (by omega), if_pos (by omega)]
  simp [coord]

theorem pubVH_rhoX (k : Fin 3) : pubVH δF b c m ρ χ (pubRhoX + k) = coord b (Quad.re _ (ρ 3)) k := by
  have hk := k.isLt
  simp only [pubVH, pubRhoX]
  erw [if_neg (by omega), dif_neg (by omega), dif_neg (by omega), if_neg (by omega), dif_pos (by omega)]
  congr 1; apply Fin.ext; simp

theorem pubVH_rhoP (k : Fin 3) : pubVH δF b c m ρ χ (pubRhoP + k) = coord b (Quad.re _ (ρ 4)) k := by
  have hk := k.isLt
  simp only [pubVH, pubRhoP]
  erw [if_neg (by omega), dif_neg (by omega), dif_neg (by omega), if_neg (by omega), dif_neg (by omega),
    dif_pos (by omega)]
  congr 1; apply Fin.ext; simp

end Coins

section Seed
variable {F K Kg : Type} [Field F] [Field K] [Algebra F K] [Fintype K] [FiniteDimensional F K] [DecidableEq F] [Field Kg]
  (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))]

theorem rlcL_zipIdx (g : K) : ∀ (n : ℕ) (l : List F),
    rlcL g n (l.map (algebraMap F K)) = ((l.zipIdx n).map fun p => g ^ p.2 * algebraMap F K p.1).sum := by
  intro n l
  induction l generalizing n with
  | nil => simp [rlcL]
  | cons a l ih => simp [rlcL, List.zipIdx_cons, ih]

/-- **The VS seed is the walk's closed-form seed** at the honest claim message. -/
theorem seedVS_eq_wkSeed (cells : List Noun) (c : P8PublicClaim) (m : ClaimMsgVS)
    (hm : HonestClaimMsg cells c m) (χ : Coins frameVS K) (W : List (NTree (GenComputeRow Kg)))
    (hW : 0 < W.length)
    (hroot : (rowAtW W 1).s = c.subject ∧ (rowAtW W 1).f = c.formula ∧ (rowAtW W 1).e = c.result) :
    seedVS (F := F) c m χ = wkSeed (F := F) W (χ cAlphaW) (χ cGamW) cells := by
  unfold seedVS wkSeed wkCur
  rw [labelF_eq_hl (F := F) cells c m hm, mul_comm]
  congr 1
  unfold Walk.curCol
  have h0 : W[1 - 1]? = some (W[0]'hW) := by simp [List.getElem?_eq_getElem hW]
  rw [h0]
  simp only [Option.map_some, Option.getD_some, nodeValH, lblVal]
  have hr := rowAtW_eq W 0 hW
  simp only [zero_add] at hr
  rw [← hr, hroot.1, hroot.2.1, hroot.2.2, rlcL_zipIdx]

theorem pubVH_lt6_eq_pubVec (cells : List Noun) (c : P8PublicClaim) (m : ClaimMsgVS)
    (hm : HonestClaimMsg cells c m) (b : Basis (Fin 3) F K) (ρ : Fin 5 → Quad (algebraMap F K δF))
    (χ : Coins frameVS K) (r0 : RowN)
    (hroot : r0.s = c.subject ∧ r0.f = c.formula ∧ r0.e = c.result) (i : ℕ) (hi : i < 6) :
    pubVH δF b c m ρ χ i = pubVec cells r0 i := by
  simp only [pubVH, if_pos hi]
  rw [labelF_eq_hl (F := F) cells c m hm, hroot.1.symm, hroot.2.1.symm, hroot.2.2.symm]
  interval_cases i <;> simp [hl, pubVec]

end Seed

section CompVS
variable {F K Kg : Type} [Field F] [Field K] [Algebra F K] [Fintype K] [FiniteDimensional F K] [DecidableEq F] [Field Kg]
  (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))]

/-- **`hcomp` at the VS verifier data.**  The honest compute trace polynomials (at the VS coins `χ`, the claim
message `x` and the requests `ρ`) are accepted by `computeChipVCLH` at `chalVH` / `pubVH`.  Discharges, from the
honest claim message and the honest terminals, every reading hypothesis of `computeChipVCLH_honest_sat`:
`hα hγ` (`chalVH` limbs), `hpIC hpS hpO` (`pubVH` limbs, the seed through `seedVS_eq_wkSeed`), `hpub6` (the claim
publics are the root handles) and `hρX hρP` (`pubVH` reads `Re ρ₃ / Re ρ₄`).  Remaining hypotheses: the walk coin
order `hord`, atoms `hat`, the priced compute pole event `hnb`, and the two terminal equations `hρ3 / hρ4`
(`Re ρ₃`, `Re ρ₄` are the compute's export / path totals). -/
theorem computeChipVCLH_honest_sat_VS {hC : ℕ} {S : MemShape} (V : VerifierData F K hC S) (x : ClaimMsgVS)
    (ρ : Fin 5 → Quad (algebraMap F K δF)) (χ : Coins frameVS K)
    {fuel : ℕ} {subject formula : Noun} {t : NTree (GenComputeRow Kg)} {result : Noun}
    (hrun : genComputeSkeleton (K := Kg) fuel subject formula = .ok (t, result)) (cells : List Noun)
    (hN : V.N = (bfsForest [airReorder t]).length)
    (hinj : Function.Injective V.computeNodes) (hadj : V.AdjacentC)
    (hcl : HonestClaimMsg cells V.claim x)
    (hroot : (rowAtW (bfsForest [airReorder t]) 1).s = V.claim.subject ∧
      (rowAtW (bfsForest [airReorder t]) 1).f = V.claim.formula ∧
      (rowAtW (bfsForest [airReorder t]) 1).e = V.claim.result)
    (hord : (bfsForest [airReorder t]).length ≤ orderOf (χ cAlphaW))
    (hρ3 : Quad.re _ (ρ 3) = accSumX V.basis cells (wRows (bfsForest [airReorder t])) (chalVH V.basis χ) V.N)
    (hρ4 : Quad.re _ (ρ 4) = accSumP V.basis cells (wRows (bfsForest [airReorder t])) (chalVH V.basis χ) V.N)
    (hat : ∀ g ∈ bfsRows (airReorder t),
      AtomsLt (ringChar F) (rowOfSkelH g.skel).sf1 ∧ AtomsLt (ringChar F) (rowOfSkelH g.skel).sf2)
    (hnb : ∀ r < V.N, NotBadRow (gE V.basis (baseEnvC cells (wRows (bfsForest [airReorder t]))
        (bfsForest [airReorder t]).length (chalVH V.basis χ) (pubVH δF V.basis V.claim x ρ χ) r))
      (baseEnvC cells (wRows (bfsForest [airReorder t])) (bfsForest [airReorder t]).length
        (chalVH V.basis χ) (pubVH δF V.basis V.claim x ρ χ) r)) :
    RAP.SatisfiesWithPreprocessing
      (computeChipVCLH V.hN V.computeNodes V.basis (chalVH V.basis χ) (pubVH δF V.basis V.claim x ρ χ) V.orbitC)
      (compPoly V.basis cells (wRows (bfsForest [airReorder t])) (bfsForest [airReorder t]).length
        (chalVH V.basis χ) (pubVH δF V.basis V.claim x ρ χ) (wkLn (χ cAlphaW))
        (wkCnt (bfsForest [airReorder t]) (χ cAlphaW))
        (wkAcc (F := F) (bfsForest [airReorder t]) (χ cAlphaW) (χ cGamW) cells) V.computeNodes
        (computeChipVCLH V.hN V.computeNodes V.basis (chalVH V.basis χ)
          (pubVH δF V.basis V.claim x ρ χ) V.orbitC).rap.w) := by
  have hW : 0 < (bfsForest [airReorder t]).length := by rw [← hN]; exact V.hN
  refine computeChipVCLH_honest_sat hrun cells (χ cAlphaW) (χ cGamW) hord V.hN hN V.computeNodes hinj V.basis
    (chalVH V.basis χ) (pubVH δF V.basis V.claim x ρ χ) V.orbitC hadj
    (limb_chal_alpha V.basis χ) (limb_chal_gamma V.basis χ) (limb_pubVH_IC δF V.basis χ V.claim x ρ)
    ((limb_pubVH_seed δF V.basis χ V.claim x ρ).trans
      (seedVS_eq_wkSeed cells V.claim x hcl χ _ hW hroot))
    (limb_pubVH_out δF V.basis χ V.claim x ρ)
    (fun i hi => pubVH_lt6_eq_pubVec δF cells V.claim x hcl V.basis ρ χ _ hroot i hi)
    (fun k => by rw [pubVH_rhoX, hρ3]) (fun k => by rw [pubVH_rhoP, hρ4]) hat hnb

end CompVS

section VZero
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP Nock.NockVMROM.Thm54.VclL.GenWalk
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq F] [Fintype K]
  {δF : F} [Fact (¬ IsSquare (algebraMap F K δF))] {hT hP hC kr : ℕ}

/-- **The 39th's honest memory datum has validity total `0`** (the `HonestVCL.vTot_eq_zero` argument:
`binds = []`, the child consumptions cancel the provides). -/
theorem HonestVCLW_vTot_eq_zero (H : HonestVCLW (K := K) δF hT hP hC kr) (χ : Coins frameVCL K) :
    H.vTot χ = 0 := by
  have := cell_vTotal (δF := δF) (γC χ) (ρC χ) (zC χ) H.d.cells [] (xs0W H.d) (xs1W H.d)
    (closureOf_nodup _) (fun n hn => closureOf_isCell hn) (fun n hn c hc => closureOf_closed hn hc)
    (fun b hb => by simp at hb)
  unfold HonestVCLW.vTot HonestVCLW.cellRows
  rw [H.hC0]
  simpa using this

/-- **Finding.**  At the VS frame, the 39th's honest datum and `GoodCVS` force `claimValSum = 0`: the
hypotheses `hρ0 : ρ 0 = H.vTot` and `GoodCVS` (`ρ 0 = claimValSum`) of `honest_accepted_VS` are jointly
satisfiable only for a vanishing claim validity sum. -/
theorem honest_VS_hyps_force_claimValSum_zero [Fintype F]
    (H : HonestVCLW (K := K) δF hT hP hC kr) (χ : Coins frameVS K) (x : ClaimMsgVS)
    (ρ : Fin 5 → Quad (algebraMap F K δF))
    (hρ0 : rho3 δF ρ 0 = H.vTot (toVCL χ)) (hGC : GoodCVS δF (vsOf H.V) x ρ χ) :
    claimValSum δF H.V.claim x χ = 0 := by
  have h1 : ρ 0 = claimValSum δF H.V.claim x χ := hGC.2.2.2.1
  rw [← h1]
  exact hρ0.trans (HonestVCLW_vTot_eq_zero H (toVCL χ))

end VZero

end

end Nock.NockVMROM.Thm54.VclL.Handle.FrameVS
