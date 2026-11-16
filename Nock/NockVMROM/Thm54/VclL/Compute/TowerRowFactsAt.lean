import Nock.NockVMROM.Thm54.VclL.Compute.TowerCompFamilyT
import Nock.NockVMROM.Thm54.P8Core.SVFrame.StandaloneGeneric

/-!
# RF-T: `rowFactsAt` at the tower compute chip

-/

namespace Nock.NockVMROM.Thm54
namespace VclL.Compute
namespace TowerD

open Nock Nock.Walk Nock.Reified Module Polynomial
open Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.T0Tower Nock.NockVMROM.Thm54.T0TowerFP
open Nock.NockVMROM.Thm54.SVFrame Nock.Framework Nock.Framework.Reify
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.VclL.Compute.WalkQ7
open Nock.NockVMROM.Thm54.VclL.Compute.NodeRecQ7
open Nock.ComputeTable (State DTcomp FP Pub fanoutComp labelVecOfPub)
open Nock.NockVMROM.Thm54.OptimizedComputeCorrectedFinal
open Nock.NockVMROM.Thm54.VclL.Compute.CoreQ7 Nock.NockVMROM.Thm54.VclL.Compute.LogUp
open Nock.NockVMROM.Thm54.VclL.Compute.CompChipVCL
open Nock.NockVMROM.Thm54.VclL.Compute.CompTreeVCL
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP (seedSpecVCL)
open Nock.NockVMROM.Thm54.VclL.Compute.SummandsQ7
open Nock.NockVMROM.Thm54.SVWalk
open Nock.NockVMROM.Thm54.OptimizedComputeSemanticRealization
open Nock.NockVMROM.Thm54.ComputeWalkSeed Nock.NockVMROM.Thm54.ComputeWalkLabel
open Nock.NockVMROM.Thm54.ComputeWalkRootEvents
open Nock.NockVMROM.Thm54.ComputePaperPacking (OneHotSelector)
open Nock.NockVMROM.Thm54.RecordCarrier
open Nock.NockVMROM.Thm54.Unhosted309 (goodSrc physOf physOf_good_round varVal)

set_option autoImplicit false
set_option maxRecDepth 300000
set_option linter.unusedSectionVars false

noncomputable section

section outside
variable {F K K' : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
  [Fintype F] [DecidableEq F] [Fintype K] [DecidableEq K]
  [Field K'] [Algebra F K'] [FiniteDimensional F K'] [Fintype K'] [DecidableEq K'] [CharP K' (ringChar K')]
  {hC : ℕ} {S : MemShape} {w : ℕ} (G : CoordGather F K')

/-- **The five carrier-free `RowFacts` core facts at every node of `treeVG`, outside the four
`𝕂′`-valued walk events** (tiling, α-root, prefix-γ), at any gather: the generic analogue of the
first half of `SummandsQ7.rowFacts_outside_core`. -/
theorem rowFacts_core_outsideG (V : VerifierData F K hC S) (chalV pubVal : ℕ → F) (Q : Fin w → F[X])
    (hadj : V.AdjacentC) (RF : RowFactsQ7 (cdOfGG G V chalV pubVal) chalV pubVal Q)
    (hchar : ∀ n : ℕ, n ≤ 11 → (n : K') = 1 → n = 1)
    (E0 : Fin V.N → Env K')
    (hcg : ∀ i q, goodSrc q = true → varVal (E0 i) q.1 q.2 =
      varVal (envsVG G V chalV pubVal Q i).toSourceEnv q.1 q.2)
    (a0 g1 z : K')
    (hα0 : alphaQ (cdOfGG G V chalV pubVal) chalV = a0)
    (hγ1 : gammaQ (cdOfGG G V chalV pubVal) chalV = g1)
    (hinit : initQ (cdOfGG G V chalV pubVal) pubVal = a0)
    (hseed : seedQ (cdOfGG G V chalV pubVal) pubVal = Walk.rlc g1 (claimLabelVec z V.claim) * a0)
    (hz : zQ (cdOfGG G V chalV pubVal) chalV ≠ 0)
    (hzi : G.chalSlot chalV 5 = (zQ (cdOfGG G V chalV pubVal) chalV)⁻¹)
    (nT : a0 ∉ tilingSetE E0 V.hN)
    (nA : a0 ∉ alphaSetE E0 V.hN g1 (claimLabelVec z V.claim))
    (nP : g1 ∉ prefixSetE E0 V.hN) :
    ∀ u, InTree (treeVG G V chalV pubVal Q) u →
      u.label.1.2.2.1.state = u.label.1.1 ∧ u.label.1.2.1.z = zQ (cdOfGG G V chalV pubVal) chalV ∧
      Nock.ComputeTable.Vcomp u.label.1.2.1 u.label.1.2.2.1 u.label.1.2.2.2 ∧
      u.children.length = fanoutComp u.label.1.1 ∧
      ∀ (k : Fin 3) (c' : NTree ((State × DTcomp K') × ℕ)), u.children[(k : ℕ)]? = some c' →
        (c'.label.1.2.2.1.s, c'.label.1.2.2.1.f, c'.label.1.2.2.1.e) =
          Nock.ComputeTable.sfTriple u.label.1.2.2.1 k := by
  obtain ⟨hl, hc, hf⟩ := sets_congr V.hN hcg
  have hRl : lblE (fun i => (envsVG G V chalV pubVal Q i).toSourceEnv) V.hN = fun i =>
      labelVecOfPub (pubAt (cdOfGG G V chalV pubVal) chalV pubVal Q RF hchar
        (rowOfG (cdOfGG G V chalV pubVal) i)) :=
    funext fun i => (decoders_eq_RFG G V chalV pubVal Q RF hchar _).1
  have hRc : chE (fun i => (envsVG G V chalV pubVal Q i).toSourceEnv) V.hN = fun i l =>
      childVecN (pubAt (cdOfGG G V chalV pubVal) chalV pubVal Q RF hchar (rowOfG (cdOfGG G V chalV pubVal) i))
        (tagsAt (cdOfGG G V chalV pubVal) chalV pubVal Q RF hchar (rowOfG (cdOfGG G V chalV pubVal) i)) (l - 1) :=
    funext fun i => funext fun l => (decoders_eq_RFG G V chalV pubVal Q RF hchar _).2.1 _
  have hRf : foE (fun i => (envsVG G V chalV pubVal Q i).toSourceEnv) V.hN =
      foW (cdOfGG G V chalV pubVal) chalV pubVal Q RF hchar :=
    funext fun i => (decoders_eq_RFG G V chalV pubVal Q RF hchar _).2.2
  have hcur : curW (cdOfGG G V chalV pubVal) chalV pubVal Q RF hchar = fun i =>
      Walk.rlc g1 (labelVecOfPub (pubAt (cdOfGG G V chalV pubVal) chalV pubVal Q RF hchar
        (rowOfG (cdOfGG G V chalV pubVal) i))) := by
    funext i; rw [curW, hγ1]
  have hchl : chldW (cdOfGG G V chalV pubVal) chalV pubVal Q RF hchar = fun i l =>
      Walk.rlc g1 (childVecN (pubAt (cdOfGG G V chalV pubVal) chalV pubVal Q RF hchar
          (rowOfG (cdOfGG G V chalV pubVal) i))
        (tagsAt (cdOfGG G V chalV pubVal) chalV pubVal Q RF hchar (rowOfG (cdOfGG G V chalV pubVal) i)) (l - 1)) := by
    funext i l; rw [chldW, hγ1]
  have htα : ¬ (alphaQ (cdOfGG G V chalV pubVal) chalV ^
        (1 + Sf (foW (cdOfGG G V chalV pubVal) chalV pubVal Q RF hchar) V.N) =
      alphaQ (cdOfGG G V chalV pubVal) chalV ^ V.N ∧
        1 + Sf (foW (cdOfGG G V chalV pubVal) chalV pubVal Q RF hchar) V.N ≠ V.N) := by
    rw [hα0, ← hRf, ← hf]
    simpa [tilingSetE] using nT
  have htile := q7_tiling (cdOfGG G V chalV pubVal) chalV pubVal Q hadj RF hchar (hinit.trans hα0.symm) htα
  have hα : alphaQ (cdOfGG G V chalV pubVal) chalV ∉ alphaBadOf (rootDiffP
      (curW (cdOfGG G V chalV pubVal) chalV pubVal Q RF hchar)
      (chldW (cdOfGG G V chalV pubVal) chalV pubVal Q RF hchar)
      (foW (cdOfGG G V chalV pubVal) chalV pubVal Q RF hchar)
      (Walk.rlc (gammaQ (cdOfGG G V chalV pubVal) chalV) (claimLabelVec z V.claim)) V.N) := by
    have hs : Sf (foE E0 V.hN) V.N + 1 = V.N := by rw [hf, hRf]; exact htile
    simp only [alphaSetE, hs, if_true] at nA
    rw [hl, hc, hf, hRl, hRc, hRf] at nA
    rw [hcur, hchl, hα0, hγ1]
    exact nA
  have hγ : gammaQ (cdOfGG G V chalV pubVal) chalV ∉ prefixBadGammas
      (fun i => labelVecOfPub (pubAt (cdOfGG G V chalV pubVal) chalV pubVal Q RF hchar
        (rowOfG (cdOfGG G V chalV pubVal) i)))
      (fun i l => childVecN (pubAt (cdOfGG G V chalV pubVal) chalV pubVal Q RF hchar
          (rowOfG (cdOfGG G V chalV pubVal) i))
        (tagsAt (cdOfGG G V chalV pubVal) chalV pubVal Q RF hchar (rowOfG (cdOfGG G V chalV pubVal) i)) (l - 1))
      (foW (cdOfGG G V chalV pubVal) chalV pubVal Q RF hchar) V.N := by
    unfold prefixSetE at nP
    rw [hl, hc, hf, hRl, hRc, hRf] at nP
    rw [hγ1]
    exact nP
  have hseed' : seedQ (cdOfGG G V chalV pubVal) pubVal =
      Walk.rlc (gammaQ (cdOfGG G V chalV pubVal) chalV) (claimLabelVec z V.claim) *
        alphaQ (cdOfGG G V chalV pubVal) chalV := by
    rw [hseed, hγ1, hα0]
  exact rowFacts_core_Q7G G V chalV pubVal Q hadj RF hchar (z := z) (hinit.trans hα0.symm) hseed' hz hzi
    hα hγ htα

end outside

/-! ## 2. The tower `f_t.leaf` / `f_th.leaf` and the `ax` gates -/

section leaf
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
  (δ : F) [Fact (¬ IsSquare (algebraMap F K δ))]

theorem fullImMap_ext41 : fullImMap.ext ⟨41, by norm_num⟩ = some 343 := by decide
theorem fullImMap_ext44 : fullImMap.ext ⟨44, by norm_num⟩ = some 352 := by decide

/-- The tower decode of `f_t.leaf`: Re window `136..138`, Im window `343..345` of the physical row. -/
theorem tower_ft_leaf (b : Basis (Fin 3) F K) (envV : Env F) :
    (StrategyOfTracesLift.decodeDec ((towerGather δ b).env309 (pullEnv envV)).base).f_t.leaf =
      Quad.mk _ (∑ k : Fin 3, envV.trace (136 + (k : ℕ)) • b k)
        (∑ k : Fin 3, envV.trace (343 + (k : ℕ)) • b k) := by
  rw [decodeDec_ft_leaf]
  show Quad.mk _ _ _ = _
  have h : towerM.ext ⟨41, by norm_num⟩ = some (343 + 95) := by
    show (fullImMap.ext ⟨41, by norm_num⟩).map (· + 95) = _
    rw [fullImMap_ext41]; rfl
  simp only [h, imVal, gatherEnv, LogUp.limbVal]
  have e1 : ∑ k : Fin 3, (pullEnv envV).trace (13 + 3 * 41 + (k : ℕ)) • b k =
      ∑ k : Fin 3, envV.trace (136 + (k : ℕ)) • b k := by
    refine Finset.sum_congr rfl fun k _ => ?_
    have : 13 + 3 * 41 + (k : ℕ) < 202 := by have := k.isLt; omega
    rw [pullEnv_trace_lt _ _ this]
  have e2 : ∑ k : Fin 3, (pullEnv envV).trace (343 + 95 + (k : ℕ)) • b k =
      ∑ k : Fin 3, envV.trace (343 + (k : ℕ)) • b k := by
    refine Finset.sum_congr rfl fun k _ => ?_
    have := vclCol_im (343 + (k : ℕ)) (by omega)
    simp only [pullEnv]
    rw [show 343 + 95 + (k : ℕ) = 343 + (k : ℕ) + 95 by omega, this]
  rw [e1, e2]

/-- The tower decode of `f_th.leaf`: Re window `145..147`, Im window `352..354` of the physical row. -/
theorem tower_fth_leaf (b : Basis (Fin 3) F K) (envV : Env F) :
    (StrategyOfTracesLift.decodeDec ((towerGather δ b).env309 (pullEnv envV)).base).f_th.leaf =
      Quad.mk _ (∑ k : Fin 3, envV.trace (145 + (k : ℕ)) • b k)
        (∑ k : Fin 3, envV.trace (352 + (k : ℕ)) • b k) := by
  rw [decodeDec_fth_leaf]
  show Quad.mk _ _ _ = _
  have h : towerM.ext ⟨44, by norm_num⟩ = some (352 + 95) := by
    show (fullImMap.ext ⟨44, by norm_num⟩).map (· + 95) = _
    rw [fullImMap_ext44]; rfl
  simp only [h, imVal, gatherEnv, LogUp.limbVal]
  have e1 : ∑ k : Fin 3, (pullEnv envV).trace (13 + 3 * 44 + (k : ℕ)) • b k =
      ∑ k : Fin 3, envV.trace (145 + (k : ℕ)) • b k := by
    refine Finset.sum_congr rfl fun k _ => ?_
    have : 13 + 3 * 44 + (k : ℕ) < 202 := by have := k.isLt; omega
    rw [pullEnv_trace_lt _ _ this]
  have e2 : ∑ k : Fin 3, (pullEnv envV).trace (352 + 95 + (k : ℕ)) • b k =
      ∑ k : Fin 3, envV.trace (352 + (k : ℕ)) • b k := by
    refine Finset.sum_congr rfl fun k _ => ?_
    have := vclCol_im (352 + (k : ℕ)) (by omega)
    simp only [pullEnv]
    rw [show 352 + 95 + (k : ℕ) = 352 + (k : ℕ) + 95 by omega, this]
  rw [e1, e2]

theorem axImGate_eval (envV : Env F) (k : Fin 3) :
    (axImGateCoord k : CoeffExpr F).eval envV =
      envV.trace 0 * envV.trace (343 + (k : ℕ)) + envV.trace 9 * envV.trace (352 + (k : ℕ)) := by
  have h1 : (fullImMap.ext 41).getD 0 = 343 := by
    have : fullImMap.ext 41 = some 343 := fullImMap_ext41
    rw [this]; rfl
  have h2 : (fullImMap.ext 44).getD 0 = 352 := by
    have : fullImMap.ext 44 = some 352 := fullImMap_ext44
    rw [this]; rfl
  simp [axImGateCoord, CoeffExpr.eval, h1, h2]

/-- **At `s0`, the tower leaf is the `𝔽`-valued axis**: the `ax` and `ax`-Im gates force
`f_t.leaf = algebraMap axCol`. -/
theorem tower_ft_leaf_ax (b : Basis (Fin 3) F K) (envV : Env F)
    (hg : ∀ g ∈ axGates b ++ axImGates, g.eval envV = 0) (h0 : envV.trace 0 = 1) (h9 : envV.trace 9 = 0) :
    (StrategyOfTracesLift.decodeDec ((towerGather δ b).env309 (pullEnv envV)).base).f_t.leaf =
      algebraMap K (Quad (algebraMap F K δ)) (algebraMap F K (envV.trace axCol)) := by
  rw [tower_ft_leaf]
  have hre := axGates_s0 b envV (fun g hg' => hg g (List.mem_append.2 (Or.inl hg'))) h0 h9
  rw [gather_ext41] at hre
  have him : ∀ k : Fin 3, envV.trace (343 + (k : ℕ)) = 0 := by
    intro k
    have := hg (axImGateCoord k) (List.mem_append.2 (Or.inr (List.mem_ofFn.2 ⟨k, rfl⟩)))
    rw [axImGate_eval, h0, h9] at this
    simpa using this
  simp only [him, zero_smul, Finset.sum_const_zero]
  rw [← Quad.mk_base]
  congr 1

theorem tower_fth_leaf_ax (b : Basis (Fin 3) F K) (envV : Env F)
    (hg : ∀ g ∈ axGates b ++ axImGates, g.eval envV = 0) (h0 : envV.trace 0 = 0) (h9 : envV.trace 9 = 1) :
    (StrategyOfTracesLift.decodeDec ((towerGather δ b).env309 (pullEnv envV)).base).f_th.leaf =
      algebraMap K (Quad (algebraMap F K δ)) (algebraMap F K (envV.trace axCol)) := by
  rw [tower_fth_leaf]
  have hre := axGates_s9 b envV (fun g hg' => hg g (List.mem_append.2 (Or.inl hg'))) h0 h9
  rw [gather_ext44] at hre
  have him : ∀ k : Fin 3, envV.trace (352 + (k : ℕ)) = 0 := by
    intro k
    have := hg (axImGateCoord k) (List.mem_append.2 (Or.inr (List.mem_ofFn.2 ⟨k, rfl⟩)))
    rw [axImGate_eval, h0, h9] at this
    simpa using this
  simp only [him, zero_smul, Finset.sum_const_zero]
  rw [← Quad.mk_base]
  congr 1

end leaf

/-! ## 3. `RowFacts.ax0` / `ax9` at the tower chip -/

section axnode
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [Fintype K]
  [DecidableEq K] [CharP K (ringChar K)] [DecidableEq F] [Fintype F] {hC : ℕ} {S : MemShape}
  (δ : F) [Fact (¬ IsSquare (algebraMap F K δ))]
  (V : VerifierData F K hC S) (chalV pubVal : ℕ → F) (Q : Fin (tableVCLT hC).width → F[X])

/-- The patched row's state is the row's (any gather). -/
theorem rowLabel_envsPG_fst {K' : Type} [Field K'] [Algebra F K'] [FiniteDimensional F K'] [DecidableEq K'] (G : CoordGather F K') (r : Fin V.N) :
    (rowLabel (envsPG G V chalV pubVal Q r)).1 = (rowLabel (envsVG G V chalV pubVal Q r)).1 := by
  rw [rowLabel_fst, rowLabel_fst]; rfl

/-- **Per-row facts the axis clauses need, at the tower chip**: the one-hot state, the decoded
state, and the `ax` / `ax`-Im gates. -/
theorem towerRow_ax_facts
    (hchar : ∀ m : ℕ, m ≤ 11 → (m : K) = 1 → m = 1)
    (hsat : RAP.SatisfiesWithPreprocessing
      (computeChipVCLQ7T V.hN V.computeNodes V.basis δ chalV pubVal V.orbitC) Q) (r : Fin V.N) :
    ∃ st, SelAt (rawEnvQ7 V chalV pubVal Q r) st ∧
      (rowLabel (envsVG (towerGather δ V.basis) V chalV pubVal Q r)).1 = st ∧
      ∀ g ∈ axGates V.basis ++ axImGates, g.eval (rawEnvQ7 V chalV pubVal Q r) = 0 := by
  have hg := ((computeChipVCLQ7T_sat_iff V.hN V.computeNodes V.basis δ chalV pubVal V.orbitC Q).1 hsat).2
    _ (by simp [rowNodeSet] : V.computeNodes r ∈ rowNodeSet V.computeNodes)
  have hh := (vclGatesQ7T_iff δ V.basis V.N _ rfl _).mp hg
  obtain ⟨st, hst⟩ := selAt_of_towerRow δ V.basis V.N _ hg hchar
  exact ⟨st, hst, rowLabel_fst_of_selAt (T := tableVCLT hC) _ V chalV pubVal Q r st hst, hh.ax⟩

variable {δ V chalV pubVal Q}

include δ in
/-- **`RowFacts.ax0` at `axB0Q7`, every node of the tower tree** (`q = ringChar 𝕂′ = ringChar 𝕂`). -/
theorem towerRowFacts_ax0 (hadj : V.AdjacentC)
    (hinj : Function.Injective V.computeNodes)
    (hchar : ∀ m : ℕ, m ≤ 11 → (m : K) = 1 → m = 1)
    (hsat : RAP.SatisfiesWithPreprocessing
      (computeChipVCLQ7T V.hN V.computeNodes V.basis δ chalV pubVal V.orbitC) Q)
    (hNp : V.N ≤ ringChar K)
    (u : NTree ((State × DTcomp (Quad (algebraMap F K δ))) × ℕ))
    (hu : InTree (treeVG (towerGather δ V.basis) V chalV pubVal Q) u) :
    u.label.1.1 = .s0 →
      (∀ n : ℕ, n < ringChar (Quad (algebraMap F K δ)) →
          u.label.1.2.2.2.f_t.leaf = (n : Quad (algebraMap F K δ)) →
          axB0Q7 V (b0 (T := tableVCLT hC) Q) (u.label.2 + 2) = n) ∧
        axB0Q7 V (b0 (T := tableVCLT hC) Q) (u.label.2 + 2) <
          ringChar (Quad (algebraMap F K δ)) := by
  intro hs0
  have hNq : V.N ≤ ringChar (Quad (algebraMap F K δ)) := by rw [ringChar_quad]; exact hNp
  obtain ⟨r, hr⟩ := treeVG_node_row (G := towerGather δ V.basis) V chalV pubVal Q u hu
  obtain ⟨st, hsel, hst, hax⟩ := towerRow_ax_facts δ V chalV pubVal Q hchar hsat r
  have hcar : rowCarrier (envsVG (towerGather δ V.basis) V chalV pubVal Q r) = r :=
    rowCarrier_eq_rowG V chalV pubVal Q (towerSerial_eq_row δ V chalV pubVal hadj Q hsat hinj) hNq r
  rw [hr] at hs0 ⊢
  simp only at hs0 ⊢
  rw [rowLabel_envsPG_fst] at hs0
  rw [show rowCarrier (envsPG (towerGather δ V.basis) V chalV pubVal Q r) =
      rowCarrier (envsVG (towerGather δ V.basis) V chalV pubVal Q r) from rfl, hcar, axB0Q7_s0,
    b0NatAt_row (T := tableVCLT hC) V chalV pubVal Q r]
  have hst0 : st = .s0 := hst ▸ hs0
  subst hst0
  have h0 : (rawEnvQ7 V chalV pubVal Q r).trace 0 = 1 := by simpa using hsel 0 (by norm_num)
  have h9 : (rawEnvQ7 V chalV pubVal Q r).trace 9 = 0 := by simpa using hsel 9 (by norm_num)
  have hK := tower_ft_leaf_ax δ V.basis _ hax h0 h9
  rw [ringChar_quad]
  refine ⟨fun n hn hleaf => ?_, natLift_lt (CharP.ringChar_ne_zero_of_finite K |>.bot_lt) _⟩
  have hleaf' : (rowLabel (envsVG (towerGather δ V.basis) V chalV pubVal Q r)).2.2.2.f_t.leaf =
      (n : Quad (algebraMap F K δ)) := by
    have hd : (rowLabel (envsPG (towerGather δ V.basis) V chalV pubVal Q r)).2.2.2 =
        (rowLabel (envsVG (towerGather δ V.basis) V chalV pubVal Q r)).2.2.2 :=
      decodeDec_lnPatch _
    rw [hd] at hleaf
    exact hleaf
  change (StrategyOfTracesLift.decodeDec (envsVG (towerGather δ V.basis) V chalV pubVal Q r)).f_t.leaf =
    (n : Quad (algebraMap F K δ)) at hleaf'
  have := hK
  change (StrategyOfTracesLift.decodeDec (envsVG (towerGather δ V.basis) V chalV pubVal Q r)).f_t.leaf = _ at this
  rw [this] at hleaf'
  have hK' : algebraMap F K ((rawEnvQ7 V chalV pubVal Q r).trace axCol) = (n : K) := by
    apply (algebraMap K (Quad (algebraMap F K δ))).injective
    rw [hleaf', map_natCast]
  exact (congrArg natLift hK').trans (natLift_natCast hn)


include δ in
/-- **`RowFacts.ax9` at `axB0Q7`, every node of the tower tree** (`q = ringChar 𝕂′ = ringChar 𝕂`). -/
theorem towerRowFacts_ax9 (hadj : V.AdjacentC)
    (hinj : Function.Injective V.computeNodes)
    (hchar : ∀ m : ℕ, m ≤ 11 → (m : K) = 1 → m = 1)
    (hsat : RAP.SatisfiesWithPreprocessing
      (computeChipVCLQ7T V.hN V.computeNodes V.basis δ chalV pubVal V.orbitC) Q)
    (hNp : V.N ≤ ringChar K)
    (u : NTree ((State × DTcomp (Quad (algebraMap F K δ))) × ℕ))
    (hu : InTree (treeVG (towerGather δ V.basis) V chalV pubVal Q) u) :
    u.label.1.1 = .s9 →
      (∀ n : ℕ, n < ringChar (Quad (algebraMap F K δ)) →
          u.label.1.2.2.2.f_th.leaf = (n : Quad (algebraMap F K δ)) →
          axB0Q7 V (b0 (T := tableVCLT hC) Q) (u.label.2 + 3) = n) ∧
        axB0Q7 V (b0 (T := tableVCLT hC) Q) (u.label.2 + 3) <
          ringChar (Quad (algebraMap F K δ)) := by
  intro hs0
  have hNq : V.N ≤ ringChar (Quad (algebraMap F K δ)) := by rw [ringChar_quad]; exact hNp
  obtain ⟨r, hr⟩ := treeVG_node_row (G := towerGather δ V.basis) V chalV pubVal Q u hu
  obtain ⟨st, hsel, hst, hax⟩ := towerRow_ax_facts δ V chalV pubVal Q hchar hsat r
  have hcar : rowCarrier (envsVG (towerGather δ V.basis) V chalV pubVal Q r) = r :=
    rowCarrier_eq_rowG V chalV pubVal Q (towerSerial_eq_row δ V chalV pubVal hadj Q hsat hinj) hNq r
  rw [hr] at hs0 ⊢
  simp only at hs0 ⊢
  rw [rowLabel_envsPG_fst] at hs0
  rw [show rowCarrier (envsPG (towerGather δ V.basis) V chalV pubVal Q r) =
      rowCarrier (envsVG (towerGather δ V.basis) V chalV pubVal Q r) from rfl, hcar, axB0Q7_s9,
    b0NatAt_row (T := tableVCLT hC) V chalV pubVal Q r]
  have hst0 : st = .s9 := hst ▸ hs0
  subst hst0
  have h0 : (rawEnvQ7 V chalV pubVal Q r).trace 0 = 0 := by simpa using hsel 0 (by norm_num)
  have h9 : (rawEnvQ7 V chalV pubVal Q r).trace 9 = 1 := by simpa using hsel 9 (by norm_num)
  have hK := tower_fth_leaf_ax δ V.basis _ hax h0 h9
  rw [ringChar_quad]
  refine ⟨fun n hn hleaf => ?_, natLift_lt (CharP.ringChar_ne_zero_of_finite K |>.bot_lt) _⟩
  have hleaf' : (rowLabel (envsVG (towerGather δ V.basis) V chalV pubVal Q r)).2.2.2.f_th.leaf =
      (n : Quad (algebraMap F K δ)) := by
    have hd : (rowLabel (envsPG (towerGather δ V.basis) V chalV pubVal Q r)).2.2.2 =
        (rowLabel (envsVG (towerGather δ V.basis) V chalV pubVal Q r)).2.2.2 :=
      decodeDec_lnPatch _
    rw [hd] at hleaf
    exact hleaf
  change (StrategyOfTracesLift.decodeDec (envsVG (towerGather δ V.basis) V chalV pubVal Q r)).f_th.leaf =
    (n : Quad (algebraMap F K δ)) at hleaf'
  have := hK
  change (StrategyOfTracesLift.decodeDec (envsVG (towerGather δ V.basis) V chalV pubVal Q r)).f_th.leaf = _ at this
  rw [this] at hleaf'
  have hK' : algebraMap F K ((rawEnvQ7 V chalV pubVal Q r).trace axCol) = (n : K) := by
    apply (algebraMap K (Quad (algebraMap F K δ))).injective
    rw [hleaf', map_natCast]
  exact (congrArg natLift hK').trans (natLift_natCast hn)

end axnode

/-! ## 4. The tower `rowFacts_outside_core` and `rowFactsAt compSoundnessVCLT` -/

section assemble
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [Fintype K]
  [DecidableEq K] [CharP K (ringChar K)] [DecidableEq F] [Fintype F] {hC : ℕ} {S : MemShape}
  (δ : F) [Fact (¬ IsSquare (algebraMap F K δ))]

theorem sumPrefixT_mem (V : VerifierData F K hC S) (tr : Traces F (tableVCLT hC) S) (χ : Coins frameVCL K) :
    (sumPrefixT δ V).mem tr χ ↔
      algebraMap K (Quad (algebraMap F K δ)) (χ ⟨1, by decide⟩) ∈ prefixSetE (srcZT δ V tr.1) V.hN := by
  unfold sumPrefixT
  refine (coinSummand_mem _ _ _ _ _ _ _ _ _).trans ?_
  exact mem_pullSet _ _

/-- **`rowFacts_outside_core` at the tower CF chip**: acceptance at `chipCFT` and a trace outside
`summandsQ7T` give `Batch1171.RowFacts` at `axB0Q7`, at the seed `z′ = (χ2, χ3)` and `q = ringChar 𝕂′`,
at every node of the tower tree. -/
theorem rowFacts_outside_CFT (V : VerifierData F K hC S) (x : ℕ → F) (ρ : Fin 3 → Quad (algebraMap F K δ))
    (χ : Coins frameVCL K) (Q : Fin (tableVCLT hC).width → F[X])
    (h : RAP.SatisfiesWithPreprocessing (chipCFT δ V x ρ χ)
      (fun j => Q (Fin.cast (chipCFT_width δ V x ρ χ) j)))
    (Qm : ∀ t : Fin S.k, Fin (S.table t).width → F[X])
    (hout : ∀ s ∈ summandsQ7T δ V, ¬ s.mem (Q, Qm) χ)
    (u : NTree ((State × DTcomp (Quad (algebraMap F K δ))) × ℕ))
    (hu : InTree (treeVG (towerGather δ V.basis) V (chalVQ7T δ V.basis χ)
      (pubVQ7T δ V.basis V.claim x χ) Q) u) :
    Nock.RedTeam.Batch1171.RowFacts (ax := axB0Q7 V (b0 (T := tableVCLT hC) Q)) (zQuad δ χ)
      (ringChar (Quad (algebraMap F K δ))) u := by
  have hg := chipCFT_good δ V x ρ χ Q h
  have hs := chipCFT_sat δ V x ρ χ Q h
  have hout0 := hout (sumZeroT δ) (by simp [summandsQ7T])
  have hz0 : zQuad δ χ ≠ 0 := fun h0 => hout0 ((sumZeroT_mem δ _ χ).2 h0)
  obtain ⟨hz, hzi⟩ := tower_z_facts δ V χ (pubCFT δ V x ρ χ) hz0
  have hu' : InTree (treeVG (towerGather δ V.basis) V (chalVQ7T δ V.basis χ) (pubCFT δ V x ρ χ) Q) u := by
    rw [treeVG_pub_irrel_T δ V _ (pubCFT δ V x ρ χ) (pubVQ7T δ V.basis V.claim x χ) Q
      (fun j hj => pubCFT_lt δ χ V x ρ j hj)]
    exact hu
  have RF := towerRowFactsQ7 δ V.hN V.computeNodes V.basis (chalVQ7T δ V.basis χ) (pubCFT δ V x ρ χ)
    V.orbitC Q hs V.claim (pubCFT δ V x ρ χ) hg.2.1
  have nT := hout (sumTilingT δ V) (by simp [summandsQ7T])
  have nA := hout (sumAlphaRootT δ V) (by simp [summandsQ7T])
  have nP := hout (sumPrefixT δ V) (by simp [summandsQ7T])
  rw [sumTilingT_mem] at nT
  rw [sumAlphaRootT_mem] at nA
  rw [sumPrefixT_mem] at nP
  have hcore := rowFacts_core_outsideG (towerGather δ V.basis) V (chalVQ7T δ V.basis χ)
    (pubCFT δ V x ρ χ) Q hg.1 RF (hcharQ_of δ hg.2.2.1) (srcZT δ V Q)
    (fun i q hq => srcVT_good δ V (fun _ _ => rfl) _ _ _ _ i q hq)
    (algebraMap K (Quad (algebraMap F K δ)) (χ ⟨0, by decide⟩))
    (algebraMap K (Quad (algebraMap F K δ)) (χ ⟨1, by decide⟩)) (zQuad δ χ)
    (chalSlot_six_T δ V.basis χ) (chalSlot_ten_T δ V.basis χ) (pubSlot_zero_T δ χ V x ρ)
    (by
      have := pubSlot_one_T δ χ V x ρ
      exact this)
    hz hzi nT nA nP u hu'
  have h1 : zQ (cdOfGG (towerGather δ V.basis) V (chalVQ7T δ V.basis χ) (pubCFT δ V x ρ χ))
      (chalVQ7T δ V.basis χ) = zQuad δ χ := chalSlot_one_T δ V.basis χ
  have hsat : RAP.SatisfiesWithPreprocessing
      (computeChipVCLQ7T V.hN V.computeNodes V.basis δ (chalVQ7T δ V.basis χ) (pubCFT δ V x ρ χ) V.orbitC) Q := hs
  exact ⟨hcore.1, hcore.2.1.trans h1, hcore.2.2.1, hcore.2.2.2.1, hcore.2.2.2.2,
    towerRowFacts_ax0 hg.1 hg.2.1 hg.2.2.1 hsat hg.2.2.2.1 u hu',
    towerRowFacts_ax9 hg.1 hg.2.1 hg.2.2.1 hsat hg.2.2.2.1 u hu'⟩

end assemble

section family
variable (F K : Type) [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [Fintype K]
  [DecidableEq K] [CharP K (ringChar K)] [Fintype F] [DecidableEq F] (hC : ℕ) (S : MemShape)
  (δ : F) [Fact (¬ IsSquare (algebraMap F K δ))]

/-- **`rowFactsAt` at the tower compute family**: the obligation `standalone_generic` took as `hrow`. -/
theorem rowFactsAt_compSoundnessVCLT : SVFrame.rowFactsAt (compSoundnessVCLT F K hC S δ) := by
  intro V x ρ χ Q h Qm hout u hu
  exact rowFacts_outside_CFT δ V x ρ χ Q h Qm hout u hu

end family

end

end TowerD
end VclL.Compute
end Nock.NockVMROM.Thm54
