import Nock.NockVMROM.Thm54.VclL.Compute.TowerAccHonest

/-!
# `honest_accepted` of the tower compute family

At the honest datum `HonestVCLT`, outside the honest bad
list `badT` (C4a's `honestBadCF`), the honest trace `traceT` satisfies the tower CF chip `chipCFT`:

* `assembled_row` (C1g/C1h) at every row, its hypotheses discharged: placement (`hch`/`hpub`/`hx0`, by
  construction), walk coins / root (`hα hγ hroot`), `hord` / `V_comp` / `WF` / `z′ ≠ 0` / the five pole conditions
  from `honestBadCF_decode` (C4a; the env is the same `envOfTrace` of the committed honest trace), the tree links
  (`NodeAxisInFormula` at every generated row);
* the remaining kept families: base (`base15_of_cells`), core `81`, aux `2`, `accInit` / `accTerminal`, the
  equality checks (`eq22_of_cells`, first / last selector banks of `xT`);
* `BindsPreprocessing` at columns `11 / 12`.
-/

namespace Nock.NockVMROM.Thm54
namespace VclL.Compute
namespace TowerD

open Nock Nock.Walk Nock.ComputeTable Nock.Reified Module
open Nock.NockVMROM.Thm54.SVFrame Nock.Framework Nock.Framework.Reify
open Nock.NockVMROM.Thm54.T0Tower Nock.NockVMROM.Thm54.CoordinateBasis
open Nock.NockVMROM.Thm54.ComputeWalkLabel Nock.NockVMROM.Thm54.TraceGen
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.OptimizedComputeCodec
open Nock.NockVMROM.Thm54.OptimizedComputeCorrectedFinal Nock.NockVMROM.Thm54.Unhosted309
open Nock.NockVMROM.Thm54.VclL.Compute.LnRead Nock.NockVMROM.Thm54.VclL.Compute.LogUp
open Nock.NockVMROM.Thm54.VclL

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxRecDepth 100000

noncomputable section

section Accept
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [Fintype K]
  [DecidableEq K] [CharP K (ringChar K)] [DecidableEq F] [Fintype F] {δ : F} [Fact (¬ IsSquare (algebraMap F K δ))]
  {hC : ℕ} {S : MemShape}

/-- The walk has `N` rows. -/
theorem walkT_len (H : HonestVCLT F K δ hC S) (χ : Coins frameVCL K) :
    H.V.N = (walkT χ H.αs H.hgen).W.length := by
  rw [H.hN]
  simp only [HonestWalk.W, walkT, honestWalkOf_root, walkRootT, genWalkRoot, bfsForest_mapNTree_singleton,
    List.length_map, bfsAssign_forest_length, nRows]

/-- The walk's row `Pub` is the rendered generator row's. -/
theorem walkT_pubAt (H : HonestVCLT F K δ hC S) (χ : Coins frameVCL K) (j : ℕ) (hj : j < H.V.N) :
    (walkT χ H.αs H.hgen).pubAt j = (renderNode (zQuad δ χ) H.αs (gRow H.t j)).row.2.2.1 := by
  simp only [walkT, honestWalkOf_pubAt, walkRootT]
  exact genWalk_bfsPubAt _ _ _ _ _ H.t j (by rw [← nRows, ← H.hN]; exact hj)

/-- `NodeAxisInFormula` at every generated row. -/
theorem gRow_axis (H : HonestVCLT F K δ hC S) (j : ℕ) (hj : j < H.V.N) : NodeAxisInFormula (gRow H.t j) := by
  have hlen : j < (Walk.bfsForest [bfsAssign (airReorder H.t)]).length := by
    rw [bfsAssign_forest_length, ← nRows, ← H.hN]; exact hj
  have hmem : (Walk.bfsForest [bfsAssign (airReorder H.t)])[j] ∈ Walk.bfsForest [bfsAssign (airReorder H.t)] :=
    List.getElem_mem hlen
  obtain ⟨c, hc, hin⟩ := (Walk.mem_bfsForest _ _).mp hmem
  simp only [List.mem_singleton] at hc
  subst hc
  have hax := genComputeSkeleton_assigned_inTree_axisInFormula H.hgen _ hin
  have e2 := congrArg (fun l => l[j]?) (bfsAssign_bfsForest_labels (airReorder H.t))
  have hr : j < (List.range' 1 (Walk.bfsForest [airReorder H.t]).length).length := by
    simp only [List.length_range']; rw [← nRows, ← H.hN]; exact hj
  simp only [List.getElem?_map, List.getElem?_eq_getElem hlen, Option.map_some,
    List.getElem?_eq_getElem hr, List.getElem_range'] at e2
  have e3 := Option.some.inj e2
  rw [e3] at hax
  unfold gRow
  convert hax using 2
  omega

/-- The kept core ids at or above `72`. -/
theorem keptCore_ge72 (g : CorrectedCoreExtGateId) (hg : g ∈ keptCoreIdsQ7) (h : ¬ g.val < 72) :
    g.val = 73 ∨ g.val = 74 ∨ g.val = 75 ∨ g.val = 76 ∨ g.val = 77 ∨ g.val = 81 := by
  have key : ∀ g ∈ keptCoreIdsQ7, 72 ≤ g.val →
      g.val = 73 ∨ g.val = 74 ∨ g.val = 75 ∨ g.val = 76 ∨ g.val = 77 ∨ g.val = 81 := by decide +kernel
  exact key g hg (by omega)

theorem coreTarget_special (g : CorrectedCoreExtGateId)
    (h : g.val = 73 ∨ g.val = 74 ∨ g.val = 75 ∨ g.val = 76 ∨ g.val = 77) : coreTarget g = specialTarget g := by
  have hs : specialCore g = true := by
    have key : ∀ g : CorrectedCoreExtGateId,
        (g.val = 73 ∨ g.val = 74 ∨ g.val = 75 ∨ g.val = 76 ∨ g.val = 77) → specialCore g = true := by
      decide +kernel
    exact key g h
  simp only [coreTarget, hs, if_true]

theorem quad_zero_re_im : Quad.re (algebraMap F K δ) 0 = 0 ∧ Quad.im (algebraMap F K δ) 0 = 0 := by
  rw [← Quad.mk_zero' (algebraMap F K δ), Quad.re_mk, Quad.im_mk]; exact ⟨rfl, rfl⟩

set_option maxHeartbeats 16000000 in
/-- **`TowerRowHolds` at every honest row** outside the honest bad list (the accumulator gates from `hacc`). -/
theorem rowHolds_T (H : HonestVCLT F K δ hC S) (χ : Coins frameVCL K)
    (Qm : ∀ t : Fin S.k, Fin (S.table t).width → Polynomial F)
    (hbad : ∀ s ∈ badT H.V H.t, ¬ s.mem (traceT H.V χ H.αs H.hgen, Qm) χ) (i : Fin H.V.N) :
    TowerRowHolds δ H.V.basis H.V.N (envT H.V χ H.αs H.hgen i) := by
  have hinj := injective_of_pow H.V H.hnodes H.hsize
  have hadj := adjacentC_of_pow H.V H.hnodes
  have hnW := walkT_len H χ
  obtain ⟨⟨hz, -⟩, hvw, hordK, hpole⟩ := honestBadCF_decode δ H.t _ le_rfl _ le_rfl H.V.N H.V.hN H.V
    (fun i => stT H.t i) (traceT H.V χ H.αs H.hgen, Qm) χ hbad
  have hord : (walkT χ H.αs H.hgen).W.length ≤ orderOf (walkT χ H.αs H.hgen).α := by
    rw [← hnW]; exact hordK
  have hvwf : ∀ j, j < H.V.N → Vcomp (towerInputs (δ := δ) χ H.αs) ((walkT χ H.αs H.hgen).pubAt j)
        (decT χ H.αs H.t j) ∧ WF (towerInputs (δ := δ) χ H.αs) ((walkT χ H.αs H.hgen).pubAt j) := by
    intro j hj
    rw [walkT_pubAt H χ j hj]
    have hr : j + 1 ∈ List.range' 1 (Walk.bfsForest [airReorder H.t]).length := by
      rw [List.mem_range']; refine ⟨by omega, ?_⟩; rw [← nRows, ← H.hN]; omega
    exact hvw H.αs H.hgen hr
  have hroot : labelVecOfPub ((walkT χ H.αs H.hgen).pubAt 0) =
      ComputeWalkSeed.claimLabelVec (zQuad δ χ) H.V.claim :=
    genHonestWalk_hroot _ _ _ _ _ H.hgen _ rfl H.V.claim rfl
  have hst : ∀ j : Fin H.V.N, (stateIndex ((walkT χ H.αs H.hgen).pubAt j).state : ℕ) = stT H.t j := by
    intro j
    rw [walkT_state χ H.αs H.hgen j (by rw [← H.hN]; exact j.isLt)]; rfl
  -- the publics read by the gates
  have hpubx : ∀ j, j < 42 → 6 ≤ j → (j < 48 ∨ 51 ≤ j) →
      pubCFT δ H.V (xT H.t) (reqT H.t χ) χ j = xT H.t j := by
    intro j h1 h2 _
    rw [pubCFT_lt δ χ H.V (xT H.t) (reqT H.t χ) j (Or.inl h1)]
    simp only [pubVQ7T, show ¬ j < 3 by omega, show ¬ (3 ≤ j ∧ j < 6) by omega,
      show ¬ (48 ≤ j ∧ j < 51) by omega, dif_neg, not_false_eq_true]
  have hx0 : ∀ j, j < 11 → xT H.t (20 + j) =
      if j = (stateIndex ((walkT χ H.αs H.hgen).pubAt 0).state : ℕ) then 1 else 0 := by
    intro j hj
    have h0 := hst ⟨0, H.V.hN⟩
    simp only at h0
    rw [h0]
    simp only [xT, show 20 ≤ 20 + j ∧ 20 + j < 31 by omega, and_self, if_true, Nat.add_sub_cancel_left]
  obtain ⟨hne0, hp0, hpe, hp6, hp9⟩ := hpole i (chalVQ7T δ H.V.basis χ)
    (pubCFT δ H.V (xT H.t) (reqT H.t χ) χ) rfl
  obtain ⟨WG, hcore, hlook, hser, hax, haxIm⟩ := assembled_row (δ := δ) H.V.basis H.V rfl (xT H.t)
    (reqT H.t χ) χ H.αs (walkT χ H.αs H.hgen) H.V.N
    (decT χ H.αs H.t) serT (axT H.t) (fIdxT H.t) (vIT H.t 1) (vIT H.t 2) (accXT H.V χ H.αs H.hgen)
    (accPT H.V χ H.αs H.hgen) H.V.computeNodes hinj H.V.orbitC.ω (chalVQ7T δ H.V.basis χ)
    (pubCFT δ H.V (xT H.t) (reqT H.t χ) χ) hnW hadj i rfl rfl hx0 rfl rfl hroot hord
    (fun j hj => (hvwf j hj).1) (fun j hj => (hvwf j hj).2) hz (fun _ => rfl) hne0
    (fun h => hp0 (by rw [← hst i]; exact h)) (fun h => hpe (by rw [← hst i]; exact h))
    (fun h => hp6 (by rw [← hst i]; exact h)) (fun h => hp9 (by rw [← hst i]; exact h))
    (gRow H.t i) (gRow_axis H i i.isLt) (walkT_pubAt H χ i i.isLt) rfl rfl
  obtain ⟨W73, W74, W75, W76, W77, Wa0, Wa1, Wln1, Wc1, Wout, Wacc⟩ := WG
  set E := envT H.V χ H.αs H.hgen i with hEdef
  have hF : ∀ c, SrcRead c → (pullEnv E).trace c = srcColT H.V.basis (rowsT H.V χ H.αs H.hgen i) c :=
    honestQT_hF H.V.basis H.V.computeNodes hinj _ H.V.orbitC.ω _ _ i
  have hFn := honestQT_hFn_final H.V.basis χ H.αs (walkT χ H.αs H.hgen) H.V.N (decT χ H.αs H.t) serT (axT H.t)
    (fIdxT H.t) (vIT H.t 1) (vIT H.t 2) (accXT H.V χ H.αs H.hgen) (accPT H.V χ H.αs H.hgen) H.V.computeNodes hinj
    H.V.orbitC.ω (chalVQ7T δ H.V.basis χ) (pubCFT δ H.V (xT H.t) (reqT H.t χ) χ) hadj i
  have vest : (rowsT H.V χ H.αs H.hgen i).ext 32 = 0 ∧ (rowsT H.V χ H.αs H.hgen i).ext 33 = 0 ∧
      (rowsT H.V χ H.αs H.hgen i).ext 34 = 0 ∧ (rowsT H.V χ H.αs H.hgen i).ext 35 = 0 ∧
      (rowsT H.V χ H.αs H.hgen i).ext 60 = 0 := genRowVals_vestige _ _ _ _ _ _ _ _ _ _ _ _ _
  obtain ⟨v32, v33, v34, v35, v60⟩ := vest
  have hsel : ∀ (j : ℕ) (hj : j < 11), (rowsT H.V χ H.αs H.hgen i).base ⟨j, by omega⟩ =
      if j = (stateIndex ((walkT χ H.αs H.hgen).pubAt i).state : ℕ) then 1 else 0 := by
    intro j hj
    rw [rowsT_base]; simp [hj]
  have h11 : (rowsT H.V χ H.αs H.hgen i).base 11 = if (i : ℕ) = 0 then 1 else 0 := by
    rw [rowsT_base]; simp
  have h12 : (rowsT H.V χ H.αs H.hgen i).base 12 = if (i : ℕ) + 1 = H.V.N then 1 else 0 := by
    rw [rowsT_base]; simp
  have cells := honestBaseCells_of_src H.V.basis (rowsT H.V χ H.αs H.hgen i) (pullEnv E) hF H.V.N i
    (stateIndex ((walkT χ H.αs H.hgen).pubAt i).state : ℕ) hsel h11 h12
  have hsLt := (stateIndex ((walkT χ H.αs H.hgen).pubAt i).state).isLt
  -- the chip next row's vestige role `32`
  have vn32 : (nextFinal χ H.αs (walkT χ H.αs H.hgen) H.V.N (decT χ H.αs H.t)
      (vclFinal H.V.basis χ H.αs (walkT χ H.αs H.hgen) H.V.N (decT χ H.αs H.t) serT (axT H.t) (fIdxT H.t)
        (vIT H.t 1) (vIT H.t 2) (accXT H.V χ H.αs H.hgen) (accPT H.V χ H.αs H.hgen) H.V.computeNodes H.V.orbitC.ω
        (chalVQ7T δ H.V.basis χ) (pubCFT δ H.V (xT H.t) (reqT H.t χ) χ))
      H.V.computeNodes H.V.orbitC.ω (chS (δ := δ) H.V.basis χ) i).ext 32 = 0 := by
    unfold nextFinal
    split_ifs with h
    · exact (genRowVals_vestige _ _ _ _ _ _ _ _ _ _ _ _ _).1
    · have hk : ∀ k, (rowFinal χ H.αs (walkT χ H.αs H.hgen) H.V.N (decT χ H.αs H.t)
          (vclFinal H.V.basis χ H.αs (walkT χ H.αs H.hgen) H.V.N (decT χ H.αs H.t) serT (axT H.t) (fIdxT H.t)
            (vIT H.t 1) (vIT H.t 2) (accXT H.V χ H.αs H.hgen) (accPT H.V χ H.αs H.hgen) H.V.computeNodes
            H.V.orbitC.ω (chalVQ7T δ H.V.basis χ) (pubCFT δ H.V (xT H.t) (reqT H.t χ) χ))
          H.V.computeNodes H.V.orbitC.ω (chS (δ := δ) H.V.basis χ) k).ext 32 = 0 := fun k =>
        (genRowVals_vestige _ _ _ _ _ _ _ _ _ _ _ _ _).1
      simp only [extRow, lagRow, hk, (quad_zero_re_im (F := F) (K := K) (δ := δ)).1,
        (quad_zero_re_im (F := F) (K := K) (δ := δ)).2, smul_zero, Finset.sum_const_zero, Quad.mk_zero']
  have hpub6 : ∀ k, k < 3 → (pullEnv E).pub (6 + k) = 0 := by
    intro k hk
    show pubCFT δ H.V (xT H.t) (reqT H.t χ) χ (6 + k) = 0
    rw [hpubx (6 + k) (by omega) (by omega) (Or.inl (by omega))]
    simp only [xT, show ¬ (20 ≤ 6 + k ∧ 6 + k < 31) by omega, show ¬ (31 ≤ 6 + k ∧ 6 + k < 42) by omega,
      if_false]
  have hb20 : ∀ j < 11, (pullEnv E).pub (20 + j) = if j = stT H.t 0 then 1 else 0 := by
    intro j hj
    show pubCFT δ H.V (xT H.t) (reqT H.t χ) χ (20 + j) = _
    rw [hpubx (20 + j) (by omega) (by omega) (Or.inl (by omega))]
    simp only [xT, show 20 ≤ 20 + j ∧ 20 + j < 31 by omega, and_self, if_true, Nat.add_sub_cancel_left]
  have hb31 : ∀ j < 11, (pullEnv E).pub (31 + j) = if j = stT H.t (nRows H.t - 1) then 1 else 0 := by
    intro j hj
    show pubCFT δ H.V (xT H.t) (reqT H.t χ) χ (31 + j) = _
    rw [hpubx (31 + j) (by omega) (by omega) (Or.inl (by omega))]
    simp only [xT, show ¬ (20 ≤ 31 + j ∧ 31 + j < 31) by omega, show 31 ≤ 31 + j ∧ 31 + j < 42 by omega,
      and_self, if_true, if_false, Nat.add_sub_cancel_left]
  have hkept : TowerKeptHolds H.V.N δ (gatherEnv H.V.basis (pullEnv E)) (pullEnv E) := by
    refine ⟨base15_of_cells H.V.N i _ i.isLt hsLt (pullEnv E) cells, ?_, ?_, ?_, ?_, ?_⟩
    · intro g hg
      by_cases hlt : g.val < 72
      · exact hcore g hg hlt
      · rcases keptCore_ge72 g hg hlt with h | h | h | h | h | h
        · rw [show g = packedWalkLnId from Fin.ext h] ; unfold towerHolds
          rw [coreTarget_special _ (Or.inl rfl)]; exact W73
        · rw [show g = ⟨74, by decide⟩ from Fin.ext h]; unfold towerHolds
          rw [coreTarget_special _ (Or.inr (Or.inl rfl))]; exact W74
        · rw [show g = ⟨75, by decide⟩ from Fin.ext h]; unfold towerHolds
          rw [coreTarget_special _ (Or.inr (Or.inr (Or.inl rfl)))]; exact W75
        · rw [show g = ⟨76, by decide⟩ from Fin.ext h]; unfold towerHolds
          rw [coreTarget_special _ (Or.inr (Or.inr (Or.inr (Or.inl rfl))))]; exact W76
        · rw [show g = ⟨77, by decide⟩ from Fin.ext h]; unfold towerHolds
          rw [coreTarget_special _ (Or.inr (Or.inr (Or.inr (Or.inr rfl))))]; exact W77
        · rw [show g = 81 from Fin.ext h]
          exact honest_core81 H.V.basis _ _ (pullEnv E) hF hFn v60 vn32
    · intro j
      fin_cases j
      · exact Wa0
      · exact Wa1
      · exact honest_vestige_aux2 H.V.basis _ (pullEnv E) hF v33 v34 v35
    · intro g hg
      rw [endpoint2Q7_eq] at hg
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl | rfl | rfl | rfl
      · exact Wln1
      · exact Wc1
      · exact Wout
      · exact honest_accInit H.V.basis _ (pullEnv E) hF v32
      · exact honest_accTerminal H.V.basis _ (pullEnv E) hF v60 hpub6
    · intro g hg
      simp only [endpoint4_309, List.mem_cons, List.not_mem_nil, or_false] at hg
      rw [hg]; exact Wacc
    · refine eq22_of_cells H.V.N i _ (stT H.t 0) (stT H.t (nRows H.t - 1)) (pullEnv E) cells hb20 hb31 ?_ ?_
      · intro h0
        have := hst i
        rw [this]
        have hi0 : i = ⟨0, H.V.hN⟩ := Fin.ext h0
        rw [hi0]
      · intro hl
        rw [hst i]
        congr 1
        rw [← H.hN]; omega
  have hlk := (lookupGatesT_iff δ H.V.basis E).mp hlook
  have hz1g : ∀ g ∈ z1Gates H.V.basis δ, g.eval E = 0 := by
    have hjn : (i : ℕ) < nRows H.t := H.hN ▸ i.isLt
    obtain ⟨hsh, -, -⟩ := gRow_facts H.hgen i hjn
    rw [hEdef, ← envsT_eq]
    exact z1Gates_row H.V χ H.αs H.hgen H.hnodes H.hsize i i.isLt hjn hsh _ _
  exact ⟨hkept, hser, fun g hg => (List.mem_append.mp hg).elim (hax g) (haxIm g), hlk.1, hlk.2.1, hlk.2.2,
    H.hacc χ Qm hbad i, hz1g⟩

/-- **The fixed columns `11 / 12` of the honest trace are the first / last-row masks.** -/
theorem binds_T (H : HonestVCLT F K δ hC S) (χ : Coins frameVCL K) :
    (computeChipVCLQ7T H.V.hN H.V.computeNodes H.V.basis δ (chalVQ7T δ H.V.basis χ)
      (pubCFT δ H.V (xT H.t) (reqT H.t χ) χ) H.V.orbitC).BindsPreprocessing (traceT H.V χ H.αs H.hgen) := by
  intro j
  fin_cases j
  · show Lagrange.interpolate Finset.univ H.V.computeNodes (vclColT H.V.basis (rowsT H.V χ H.αs H.hgen) 11) =
      firstRowMask H.V.computeNodes
    unfold firstRowMask
    congr 1
  · show Lagrange.interpolate Finset.univ H.V.computeNodes (vclColT H.V.basis (rowsT H.V χ H.αs H.hgen) 12) =
      lastRowMask H.V.hN H.V.computeNodes
    unfold lastRowMask
    congr 1
    funext i
    simp only [vclColT, show (12 : ℕ) < 202 by norm_num, if_true, srcColT, show (12 : ℕ) < 13 by norm_num,
      dif_pos, rowsT_base]
    have hi := i.isLt
    by_cases h : (i : ℕ) + 1 = H.V.N
    · rw [if_pos (Fin.ext (by simp only; omega))]; simp [h]
    · have hne : ¬ i = ⟨H.V.N - 1, Nat.sub_lt H.V.hN (by omega)⟩ := by
        intro he
        apply h
        have h2 : (i : ℕ) = H.V.N - 1 := by rw [he]
        have := H.V.hN
        omega
      rw [if_neg hne]; simp [h]

/-- **`honest_accepted`** (the frame field's shape): outside the honest bad list, the tower CF chip at the honest
datum accepts the honest trace. -/
theorem honest_accepted_T (H : HonestVCLT F K δ hC S) (χ : Coins frameVCL K)
    (Qm : ∀ t : Fin S.k, Fin (S.table t).width → Polynomial F)
    (hbad : ∀ s ∈ badT H.V H.t, ¬ s.mem (traceT H.V χ H.αs H.hgen, Qm) χ) :
    RAP.SatisfiesWithPreprocessing (chipCFT δ H.V (xT H.t) (reqT H.t χ) χ)
      (fun j => traceT H.V χ H.αs H.hgen (Fin.cast (chipCFT_width δ H.V (xT H.t) (reqT H.t χ) χ) j)) := by
  have hg := goodCFT_honest δ H.V H.hnodes H.hsize H.hp H.hrowsC (reqT H.t χ) rfl
  have hsat : RAP.SatisfiesWithPreprocessing (computeChipVCLQ7T H.V.hN H.V.computeNodes H.V.basis δ
      (chalVQ7T δ H.V.basis χ) (pubCFT δ H.V (xT H.t) (reqT H.t χ) χ) H.V.orbitC) (traceT H.V χ H.αs H.hgen) := by
    refine computeChipVCLQ7T_of_rowHolds H.V.hN H.V.computeNodes H.V.basis δ _ _ H.V.orbitC _ (binds_T H χ) ?_
    intro x hx
    simp only [rowNodeSet, Finset.mem_image, Finset.mem_univ, true_and] at hx
    obtain ⟨i, rfl⟩ := hx
    exact rowHolds_T H χ Qm hbad i
  have hc : chipCFT δ H.V (xT H.t) (reqT H.t χ) χ = computeChipVCLQ7T H.V.hN H.V.computeNodes H.V.basis δ
      (chalVQ7T δ H.V.basis χ) (pubCFT δ H.V (xT H.t) (reqT H.t χ) χ) H.V.orbitC := by
    unfold chipCFT; exact if_pos hg
  have key : ∀ c : FixedPreprocessingRAP F, c = computeChipVCLQ7T H.V.hN H.V.computeNodes H.V.basis δ
      (chalVQ7T δ H.V.basis χ) (pubCFT δ H.V (xT H.t) (reqT H.t χ) χ) H.V.orbitC →
      ∀ hw : c.rap.w = (tableVCLT hC).width,
      RAP.SatisfiesWithPreprocessing c (fun j => traceT H.V χ H.αs H.hgen (Fin.cast hw j)) := by
    intro c hc hw
    subst hc
    exact hsat
  exact key _ hc _

end Accept

end

end TowerD
end VclL.Compute
end Nock.NockVMROM.Thm54
